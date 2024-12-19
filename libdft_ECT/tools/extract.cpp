#include "branch_pred.h"
#include "libdft_api.h"
#include "pin.H"
#include "syscall_desc.h"
#include "tagmap.h"
#include "debug.h"
#include <iostream>
#include <set>
#include <sys/syscall.h>
#include <unistd.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <cstring>
#include <sys/socket.h>
#include <netinet/in.h>
#include <arpa/inet.h>
#include <sys/mman.h>
#include "syscall_struct.h"
#include "ssa_tag.h"
#include "vector"
#include "map"
#include "algorithm"
#include <tuple>
#include "string"
#include "dwarf.h"
#include "libdwarf.h"
#include "json/json.hpp"
#include <fstream>
#include <sstream>
#include <sys/shm.h>

using json = nlohmann::json;

KNOB<BOOL> KnobIsExtract(KNOB_MODE_WRITEONCE, "pintool", "ex", "1", "is extract mode?");
KNOB<string> KnobTraceFile(KNOB_MODE_WRITEONCE, "pintool", "trFile", "tr.json", "trace file");
KNOB<string> KnobExtractFile(KNOB_MODE_WRITEONCE, "pintool", "exFile", "ex.json", "input extract file");
/*
 *===========================================================================
 *                          Taint Source Related
 *===========================================================================
 */

uint64_t g_tag_off = 0;
extern syscall_desc_t syscall_desc[SYSCALL_MAX];

struct fdInfo
{
    string fileName;
    vector<tuple<uint64_t, uint64_t, uint64_t>> regions;
    uint64_t refCount;

    tuple<uint64_t, uint64_t, uint64_t> *getRegion(uint64_t tag_off)
    {
        for (auto &item : regions)
        {
            uint64_t g_tag_off = std::get<1>(item);
            uint64_t len = std::get<2>(item);
            if (tag_off >= g_tag_off && tag_off < g_tag_off + len)
                return &item;
        }
        return nullptr;
    }

    bool isContain(uint64_t tag_off)
    {
        return getRegion(tag_off) != nullptr;
    }

    uint64_t getFileOffset(uint64_t tag_off)
    {
        auto t = getRegion(tag_off);
        uint64_t file_off = std::get<0>(*t);
        uint64_t g_tag_off = std::get<1>(*t);
        return tag_off - g_tag_off + file_off;
    }
};

// allFiles中保存了所有正在打开和曾经打开过的文件的fdInfo信息
vector<fdInfo *> allFdInfos;

// fdInfoMap仅保存当前正打开的fd和对应的fdInfo信息
map<int, fdInfo *> fdInfoMap;

fdInfo *getFdInfo(uint64_t tag_off)
{
    for (fdInfo *fi : allFdInfos)
    {
        if (fi->isContain(tag_off))
            return fi;
    }
    // tag off必然对应一个fdinfo
    cerr << "error: " << tag_off << " not in any fdInfo" << endl;
    assert(false);

    return nullptr;
}

bool inBlackList(string fileName)
{
    return fileName.find(".so") != string::npos;
}

static void post_open_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const int fd = ctx->ret;
    if (unlikely(fd < 0))
        return;
    const char *file_name = (char *)ctx->arg[SYSCALL_ARG0];
    if (inBlackList(file_name))
        return;

    fdInfoMap[fd] = new fdInfo();
    fdInfoMap[fd]->fileName = file_name;
    fdInfoMap[fd]->refCount = 1;
    allFdInfos.push_back(fdInfoMap[fd]);
}

static void post_openat_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const int fd = ctx->ret;
    if (unlikely(fd < 0))
        return;
    const char *file_name = (char *)ctx->arg[SYSCALL_ARG1];
    if (inBlackList(file_name))
        return;
    fdInfoMap[fd] = new fdInfo();
    fdInfoMap[fd]->fileName = file_name;
    fdInfoMap[fd]->refCount = 1;
    allFdInfos.push_back(fdInfoMap[fd]);
}

static void post_dup_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const int ret = ctx->ret;
    if (ret < 0)
        return;
    const int old_fd = ctx->arg[SYSCALL_ARG0];
    auto it = fdInfoMap.find(old_fd);
    if (it != fdInfoMap.end())
    {
        fdInfoMap[ret] = fdInfoMap[old_fd];
        fdInfoMap[ret]->refCount++;
    }
}

static void post_dup2_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const int ret = ctx->ret;
    if (ret < 0)
        return;
    const int old_fd = ctx->arg[SYSCALL_ARG0];
    const int new_fd = ctx->arg[SYSCALL_ARG1];
    auto it = fdInfoMap.find(old_fd);
    if (it != fdInfoMap.end())
    {
        fdInfoMap[new_fd] = fdInfoMap[old_fd];
        fdInfoMap[old_fd]->refCount++;
    }
}

static void post_close_hook(THREADID tid, syscall_ctx_t *ctx)
{
    if (unlikely((long)ctx->ret < 0))
        return;
    const int fd = ctx->arg[SYSCALL_ARG0];
    auto it = fdInfoMap.find(fd);
    if (likely(it != fdInfoMap.end()))
    {
        fdInfoMap[fd]->refCount--;
        fdInfoMap.erase(it);
    }
}

/*
这里有两点可以调整的地方：
1。保存返回值的rax是否应该设置tag
2。read的count参数比实际读取字节数大时，没有读到的部分是否应该设置tag（这部分
区域可能潜在的属于用户可以控制的区域）
 */
static void post_read_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const size_t nr = ctx->ret;
    if (unlikely((long)nr <= 0))
        return;
    const int fd = ctx->arg[SYSCALL_ARG0];
    const ADDRINT buf = ctx->arg[SYSCALL_ARG1];
    if (fdInfoMap.find(fd) != fdInfoMap.end())
    {
        uint64_t read_off = lseek(fd, 0, SEEK_CUR) - nr;
        fdInfoMap[fd]->regions.push_back(tuple<uint64_t, uint64_t, uint64_t>(read_off, g_tag_off, nr));
        for (unsigned int i = 0; i < nr; i++)
        {
            tag_t t = tag_alloc<tag_t>(g_tag_off++, tid);
            tagmap_setb(buf + i, t);
        }
        //cerr << "readed " << nr << " tainted from" << fdInfoMap[fd]->fileName << "\n";
    }
    else
    {
        tagmap_clrn(buf, nr);
    }
}

static void post_pread64_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const size_t nr = ctx->ret;
    if (unlikely((long)nr <= 0))
        return;
    const int fd = ctx->arg[SYSCALL_ARG0];
    const ADDRINT buf = ctx->arg[SYSCALL_ARG1];
    if (fdInfoMap.find(fd) != fdInfoMap.end())
    {
        unsigned int read_off = ctx->arg[SYSCALL_ARG3];
        fdInfoMap[fd]->regions.push_back(tuple<uint64_t, uint64_t, uint64_t>(read_off, g_tag_off, nr));
        for (unsigned int i = 0; i < nr; i++)
        {
            tag_t t = tag_alloc<tag_t>(g_tag_off++, tid);
            tagmap_setb(buf + i, t);
        }
        cerr << "readed " << nr << " tainted\n";
    }
    else
    {
        tagmap_clrn(buf, nr);
    }
}

static void post_readv_hook(THREADID tid, syscall_ctx_t *ctx)
{
    if (unlikely((long)ctx->ret <= 0))
        return;

    const int fd = (int)ctx->arg[SYSCALL_ARG0];
    size_t bytes_readed = (size_t)ctx->ret;
    uint64_t read_off = lseek(fd, 0, SEEK_CUR) - bytes_readed;
    auto it = fdInfoMap.find(fd);
    if (it != fdInfoMap.end())
        fdInfoMap[fd]->regions.push_back(tuple<uint64_t, uint64_t, uint64_t>(read_off, g_tag_off, bytes_readed));

    for (int i = 0; bytes_readed > 0; i++)
    {
        struct iovec *iov = ((struct iovec *)ctx->arg[SYSCALL_ARG1]) + i;
        size_t iov_readed = (bytes_readed >= iov->iov_len) ? iov->iov_len : bytes_readed;

        if (it != fdInfoMap.end())
        {
            fprintf(stderr, "readbuf at %p\n", iov->iov_base);
            for (size_t i = 0; i < iov_readed; i++)
            {
                tag_t t = tag_alloc<tag_t>(g_tag_off++, tid);
                tagmap_setb(((ADDRINT)iov->iov_base) + i, t);
            }
        }
        else
        {
            tagmap_clrn((size_t)iov->iov_base, iov_readed);
        }
        bytes_readed -= iov_readed;
    }
}

/* static void post_mmap_hook(THREADID tid, syscall_ctx_t *ctx)
{
    const ADDRINT ret = ctx->ret;
    const int prot = ctx->arg[SYSCALL_ARG2];
    if ((void *)ret == (void *)MAP_FAILED || !(prot & PROT_READ))
        return;

    size_t len = (size_t)ctx->arg[SYSCALL_ARG1];
    ADDRINT addr = ctx->ret;

    const int fd = ctx->arg[SYSCALL_ARG4];
    const off_t read_off = ctx->arg[SYSCALL_ARG5];

    if (unlikely(len % PAGE_SZ != 0))
        len = len - (len % PAGE_SZ) + PAGE_SZ;

    if (unlikely((int)ctx->arg[SYSCALL_ARG3] & MAP_GROWSDOWN))
        addr -= len;

    if (fdInfoMap.find(fd) != fdInfoMap.end())
    {
        // 文件可映射大小可能小于len
        fdInfoMap[fd]->regions.push_back(tuple<uint64_t, uint64_t, uint64_t>(read_off, g_tag_off, len));
        for (unsigned int i = 0; i < len; i++)
        {
            tag_t t = tag_alloc<tag_t>(g_tag_off++, tid);
            tagmap_setb(addr + i, t);
        }
    }
    else
    {
        tagmap_clrn(addr, len);
    }

} */

/*
 *===========================================================================
 *                         Run Time Info Related
 *===========================================================================
 */
struct taintResult
{
    uint32_t offset;
    uint16_t hint;
    uint16_t groupId;
};

struct taintResultInfo
{
    uint32_t itemNum;
    taintResult items[];
};

enum NodeType
{
    FLAT,      // 基本类型和子元素均为FLAT类型的结构体类型
    POINTER,   // 指针类型，被指对象在subType中(注意可能是数组)
    AGGREGATE, // 聚合类型，各个子字段在subType中
    FUNCTION,  // 函数类型
    UNKNOWN    // 未知类型
};

struct TypeInfoNode
{
    uint64_t id = 0;
    NodeType kind = NodeType::UNKNOWN;
    uint64_t size = 0;
    std::vector<std::pair<uint64_t, uint64_t>> subTypeInfos;
};

enum VarType
{
    FORMAL_PARAM,
    LOCAL_VARIABLE,
    STATIC_VARIABLE,
    GLOBAL_VARIABLE
};

/*
这里保存每个参数的污点信息，在解析参数结构时的：
    1.type offset stack，每个值对应subtype的offset，当subtype为POINTER
    或AGGREGATE时填入对应offset。
    2.tainted offset buf，在遍历检查FLAT类型对象时，所有受到输入影响的字节的下标。
    3.FLAT对象内容
当遇到需要保存污点信息时，当前的type offset stack，tainted offset buf和FLAT对象内容
会被保存到ArgInfo中。在fuzz时，根据type offset stack找到待比较FLAT位置，之后比较tainted offset buf
位置上当前内容和原FLAT内容，并进行评估。当需要变异时，根据这些位置上tag的值来确定变异位置
 */
struct ArgInfo
{
    uint64_t taintBytes = 0;
    uint64_t argIdx;
    vector<set<uint32_t>> taintSource_buf;
    vector<vector<uint64_t>> tnid_buf;
    vector<pair<vector<uint64_t>, string>> content_buf;

    void show()
    {
        for (size_t i = 0; i < taintSource_buf.size(); i++)
        {
            set<uint32_t> &offset_buf = taintSource_buf[i];
            vector<uint64_t> &tnids = tnid_buf[i];
            vector<uint64_t> &content_offset_buf = content_buf[i].first;
            cerr << "taint " << i << " :tnids:{";
            for (uint64_t tnid : tnids)
            {
                cerr << " " << tnid;
            }
            cerr << " },platOffsets:{";
            auto it2 = content_offset_buf.begin();
            if (it2 != content_offset_buf.end())
            {
                uint64_t start_offset = *it2;
                uint64_t last_offset = *it2;
                it2++;

                while (it2 != content_offset_buf.end())
                {
                    uint64_t curr_offset = *it2;
                    if (curr_offset == last_offset + 1)
                    {
                        last_offset = curr_offset;
                        it2++;
                        continue;
                    }

                    // 分段条件已经满足
                    fprintf(stderr, "[%lu-%lu]", start_offset, last_offset);

                    start_offset = curr_offset;
                    last_offset = curr_offset;
                    it2++;
                }
                fprintf(stderr, "[%lu-%lu]", start_offset, last_offset);
            }
            cerr << " },taintSources:{";
            auto it = offset_buf.begin();
            if (it != offset_buf.end())
            {
                uint64_t start_offset = *it;
                uint64_t last_offset = *it;
                fdInfo *last_fdInfo = getFdInfo(last_offset);
                it++;

                while (it != offset_buf.end())
                {
                    uint64_t curr_offset = *it;
                    fdInfo *curr_fdInfo = getFdInfo(curr_offset);
                    if (curr_offset == last_offset + 1 && curr_fdInfo == last_fdInfo)
                    {
                        last_offset = curr_offset;
                        it++;
                        continue;
                    }

                    // 分段条件已经满足
                    uint64_t last_file_start = last_fdInfo->getFileOffset(start_offset);
                    uint64_t last_file_end = last_file_start + last_offset - start_offset;
                    fprintf(stderr, "[%s:%lu-%lu]", last_fdInfo->fileName.c_str(), last_file_start, last_file_end);

                    start_offset = curr_offset;
                    last_offset = curr_offset;
                    last_fdInfo = curr_fdInfo;
                    it++;
                }
                uint64_t last_file_start = last_fdInfo->getFileOffset(start_offset);
                uint64_t last_file_end = last_file_start + last_offset - start_offset;
                fprintf(stderr, "[%s:%lu-%lu]", last_fdInfo->fileName.c_str(), last_file_start, last_file_end);
            }
            cerr << " },platData:{" << content_buf[i].second << "}\n";
            // cerr << " }\n";
        }
    }
};

struct VarInfo
{
    string name;
    VarType type;
    uint64_t typeDescId;
    int64_t addr;
};

struct FuncInfo
{
    std::string name;
    uint64_t prologueEndAddr;
    std::vector<VarInfo> varInfos;
};

struct CompareItem
{
    uint64_t argIdx;
    vector<uint64_t> tnid_buf;
    vector<uint64_t> offsets;
    char *data;
    uint32_t length;
};

struct TraceInfo
{
    TraceInfo *parent;
    std::vector<TraceInfo *> callees;
    uint32_t trackIdx = 0;
    string name;
    std::vector<ArgInfo> argInfos;
    std::vector<CompareItem> compItems;
    uint64_t trid;
};

// 应用线程必须只有1个，否则可能产生条件竞争
vector<VarInfo> globalVarInfos;
std::map<uint64_t, TypeInfoNode> TypeInfoMap;
std::map<std::string, FuncInfo> FuncInfoMap;
std::vector<TraceInfo> ApiTraces;
TraceInfo *currentTraceRoot;

// Size Map用于保存指针指向的类数组结构的大小，这些结构可能来自于堆，栈或全局
std::map<uint64_t, uint64_t> SizeMap;
uint64_t pendingSize;
vector<FuncInfo *> offTrackStack;
uint64_t callDepth = 0;
uint64_t trid = 0;
uint64_t Taint_item = 0;
uint64_t Max_Taint_item = 200;
taintResultInfo *shm_ptr;
bool noAFLmode = false;
std::map<uint32_t, uint16_t> taintResultMap;
uint32_t taintResultGroupId = 0;

uint64_t compareParam(TypeInfoNode *tn, int64_t paramAddr, uint64_t tnid_idx, CompareItem *ci)
{
    switch (tn->kind)
    {
    case NodeType::FLAT:
    {
        uint64_t score = 0;
        for (uint64_t offset : ci->offsets)
        {
            assert(offset < ci->length);
            if (offset < tn->size && ci->data[offset] == *((char *)(paramAddr + offset)))
                score += 1;
            else
            {
                if (Taint_item > Max_Taint_item)
                    continue;
                if (offset < tn->size)
                {
                    tag_t tag = tagmap_getb(paramAddr + offset);
                    if (!tag_is_empty(tag))
                    {
                        set<uint32_t> taintSource_buf;
                        ssa_tag2set(tag, taintSource_buf);
                        if (taintSource_buf.size() == 1)
                        {
                            uint32_t tag_off = *taintSource_buf.begin();
                            uint32_t input_offset = getFdInfo(tag_off)->getFileOffset(tag_off);
                            if (taintResultMap.find(input_offset) == taintResultMap.end())
                                taintResultMap[input_offset] = (uint8_t)ci->data[offset];
                        }
                        else
                        {
                            for (uint32_t tag_off : taintSource_buf)
                            {
                                uint32_t input_offset = getFdInfo(tag_off)->getFileOffset(tag_off);
                                if (taintResultMap.find(input_offset) == taintResultMap.end())
                                    taintResultMap[input_offset] = 0xffff;
                            }
                        }

                        /*                         cerr << "argIdx:"<<ci->argIdx<<" tnid:";
                                                for(uint64_t tnid:ci->tnid_buf)
                                                {
                                                    cerr << " "<<tnid;
                                                }
                                                cerr << " plat offset:"<<offset;
                                                fprintf(stderr," target:%hhx-actual:%hhx taintSource:",ci->data[offset],*((char *)(paramAddr + offset)));
                                                for (uint32_t offset : taintSource_buf)
                                                    fprintf(stderr,"0x%x,",offset);
                                                cerr << "\n"; */
                        /*                             for (auto &item : taintResultMap)
                            {
                                fprintf(stderr, "offset:0x%x,hint:%hx\n", item.first, item.second);
                            } */
                    }
                }
            }
        }
        return score;
        break;
    }
    case NodeType::POINTER:
    {
        // 仅检查被指向内存区域，因此我们不在意pointer自身位于reg中还是memory中
        TypeInfoNode *subTn = &TypeInfoMap[tn->subTypeInfos[0].second];

        // 如果指针指向函数或未知结构，则直接返回
        if (subTn->kind == NodeType::FUNCTION ||
            subTn->kind == NodeType::UNKNOWN)
            return 0;

        uint64_t subAddr = *(uint64_t *)paramAddr;
        TypeInfoNode tmpTN;
        // 我们假设指针只有悬空和正常指向两种状态
        if (subAddr == 0)
            return 0;

        auto it = SizeMap.find(subAddr);
        if (it == SizeMap.end())
        {
            // 我们缺失运行时对象大小的信息，只能使用类型分析中的结果
            // fprintf(stderr, "tnid:%lu pointer 0x%lx with unknown runtime
            // size\n",subTn->id, subAddr);
        }
        else
        {
            uint64_t size = (*it).second;
            // fprintf(stderr,"pointer 0x%lx with known size %lu\n", subAddr, size);
            //  这可能是个数组，此时大小根据运行时信息确定
            if (subTn->size != size)
            {
                if (subTn->kind == NodeType::FLAT)
                {
                    tmpTN.kind = NodeType::FLAT;
                    tmpTN.size = size;
                    subTn = &tmpTN;
                }
                else if (subTn->kind == NodeType::AGGREGATE)
                {
                    // TODO,在这里遍历整个结构体数组
                    // fprintf(stderr, "tnid:%lu aggregate array pointer,runtime size:
                    // %lu\n", subTn->id, size);
                }
                // 如果subType是指针数组，我们不对其进行统计，因为指针值不被认定为tainted
            }
        }
        return compareParam(subTn, subAddr, tnid_idx + 1, ci);
        break;
    }
    case NodeType::AGGREGATE:
    {
        // 只检查POC中存在参考的字段
        uint64_t subOffset = tn->subTypeInfos[ci->tnid_buf[tnid_idx]].first;
        TypeInfoNode *subTn =
            &TypeInfoMap[tn->subTypeInfos[ci->tnid_buf[tnid_idx]].second];
        int64_t subAddr = paramAddr + subOffset;
        return compareParam(subTn, subAddr, tnid_idx + 1, ci);
        break;
    }

    case NodeType::FUNCTION:
    case NodeType::UNKNOWN:
        break;
    default:
        break;
    }
    assert(false);
    return 0;
}

/*
根据shm_ptr的信息，给出污点分析的结果
 */
void onPrologueEnd(uint64_t rbp, FuncInfo *fi)
{
    if (!offTrackStack.empty())
    {
        offTrackStack.push_back(fi);
        // cerr << "add off tr " << fi->name << "\n";
    }
    else
    {
        TraceInfo *ti = nullptr;
        /*
        我们保留在这个层级中，之前比较过的位置，在进一步比较时，优先选择之后的条目。
        如果找不到，则尝试从之前的条目中寻找。
         */
        for (size_t i = currentTraceRoot->trackIdx; i < currentTraceRoot->callees.size(); i++)
        {
            if (currentTraceRoot->callees[i]->name == fi->name)
            {
                ti = currentTraceRoot->callees[i];
                currentTraceRoot->trackIdx = i + 1;
                break;
            }
        }
        if (ti == nullptr)
        {
            for (size_t i = 0; i < currentTraceRoot->trackIdx; i++)
            {
                if (currentTraceRoot->callees[i]->name == fi->name)
                {
                    ti = currentTraceRoot->callees[i];
                }
            }
        }
        // 如果找到了比较对象，则分析当前输入和trace的差异，否则跳过分析
        if (ti != nullptr)
        {
            currentTraceRoot = ti;
            for (CompareItem &ci : ti->compItems)
            {
                VarInfo &vi = fi->varInfos[ci.argIdx];
                TypeInfoNode *tn = &TypeInfoMap[vi.typeDescId];
                set<uint32_t> taintSource_buf;
                uint64_t score = compareParam(tn, rbp + vi.addr, 0, &ci);
                if (score != ci.offsets.size())
                {
                    // fprintf(stderr,"not equal here! %lu-%lu\n",score,ci.offsets.size());
                }

                // del with taintSource
                /* for (uint32_t offset : taintSource_buf)
                {
                    cerr << offset << " ";
                }
                cerr << "\n"; */
            }

            for (VarInfo &vi : fi->varInfos)
            {
                TypeInfoNode *tn = &TypeInfoMap[vi.typeDescId];
                if (vi.type == VarType::LOCAL_VARIABLE)
                {
                    SizeMap[rbp + vi.addr] = tn->size;
                }
            }
        }
        else
        {
            offTrackStack.push_back(fi);
            // cerr << "currentTraceRoot trid:" << currentTraceRoot->trid << "\n";
        }
    }

    for (size_t i = 0; i < callDepth; i++)
    {
        // cerr << "\t";
    }
    if (offTrackStack.empty())
    {
        cerr << "f: " << fi->name << endl;
        for (auto &item : taintResultMap)
        {
            fprintf(stderr, "offset:0x%x,hint:%hx\n", item.first, item.second);
            taintResult *tr = &shm_ptr->items[shm_ptr->itemNum++];
            tr->groupId = taintResultGroupId;
            tr->offset = item.first;
            tr->hint = item.second;
        }
        taintResultMap.clear();
        taintResultGroupId++;
    }
    else
    {
        // cerr << "f: " << fi->name << " not compared! ->"<< endl;
    }

    callDepth++;
}

void onFunctionEnd(uint64_t rbp, FuncInfo *fi)
{
    if (!offTrackStack.empty())
    {
        offTrackStack.pop_back();
    }
    else
    {
        for (VarInfo &vi : fi->varInfos)
        {
            if (vi.type == VarType::LOCAL_VARIABLE)
            {
                SizeMap.erase(rbp + vi.addr);
            }
        }
        assert(currentTraceRoot->name == fi->name);
        currentTraceRoot = currentTraceRoot->parent;
    }
    callDepth--;
    /*     for (size_t i = 0; i < callDepth; i++)
    {
        cerr << "\t";
    }
    cerr << "f: " << currentTraceRoot->name << " end\n"; */
}

void analysisParam(TypeInfoNode *tn, int64_t paramAddr, ArgInfo &ti, vector<uint64_t> &subTypeOffstack)
{
    switch (tn->kind)
    {
    case NodeType::FLAT:
    {
        vector<uint64_t> taintOffset;
        set<uint32_t> taintSource;
        for (size_t i = 0; i < tn->size; i++)
        {
            tag_t tag = tagmap_getb(paramAddr + i);
            if (!tag_is_empty(tag))
            {
                // cerr << ssa_tag_print(tag);
                taintOffset.push_back(i);
                ti.taintBytes++;
                ssa_tag2set(tag, taintSource);
            }
        }
        if (!taintOffset.empty())
        {
            char *flatStrBuf = (char *)malloc(tn->size * 2 + 1);
            char *flatContentBuf = (char *)paramAddr;
            const char *hex = "0123456789ABCDEF";
            size_t i = 0;
            for (; i < tn->size; ++i)
            {
                flatStrBuf[i * 2] = hex[(flatContentBuf[i] >> 4) & 0xf];
                flatStrBuf[i * 2 + 1] = hex[flatContentBuf[i] & 0xf];
            }
            flatStrBuf[i * 2] = 0;

            ti.content_buf.push_back(pair<vector<uint64_t>, string>(taintOffset, flatStrBuf));
            ti.tnid_buf.push_back(subTypeOffstack);
            ti.taintSource_buf.push_back(taintSource);
            free(flatStrBuf);
        }

        break;
    }
    case NodeType::POINTER:
    {
        // 仅检查被指向内存区域，因此我们不在意pointer自身位于reg中还是memory中
        TypeInfoNode *subTn = &TypeInfoMap[tn->subTypeInfos[0].second];

        // 如果指针指向函数或未知结构，则直接返回
        if (subTn->kind == NodeType::FUNCTION || subTn->kind == NodeType::UNKNOWN)
        {
            return;
        }

        uint64_t subAddr = *(uint64_t *)paramAddr;
        TypeInfoNode tmpTN;
        // 我们假设指针只有悬空和正常指向两种状态
        if (subAddr == 0)
            return;
        auto it = SizeMap.find(subAddr);
        if (it == SizeMap.end())
        {
            // fprintf(stderr, "tnid:%lu pointer 0x%lx with unknown runtime size\n", subTn->id, subAddr);
        }
        else
        {
            uint64_t size = (*it).second;
            // fprintf(stderr,"pointer 0x%lx with known size %lu\n", subAddr, size);
            //  这可能是个数组，此时大小根据运行时信息确定
            if (subTn->size != size)
            {
                if (subTn->kind == NodeType::FLAT)
                {
                    tmpTN.kind = NodeType::FLAT;
                    tmpTN.size = size;
                    subTn = &tmpTN;
                }
                else if (subTn->kind == NodeType::AGGREGATE)
                {
                    // TODO,在这里遍历整个结构体数组
                    // fprintf(stderr, "tnid:%lu aggregate array pointer,runtime size: %lu\n", subTn->id, size);
                }
                // 如果subType是指针数组，我们不对其进行统计，因为指针值不被认定为tainted
            }
        }
        subTypeOffstack.push_back(0);
        analysisParam(subTn, subAddr, ti, subTypeOffstack);
        subTypeOffstack.pop_back();
        break;
    }
    case NodeType::AGGREGATE:
        for (size_t i = 0; i < tn->subTypeInfos.size(); i++)
        {
            uint64_t subOffset = tn->subTypeInfos[i].first;
            TypeInfoNode *subTn = &TypeInfoMap[tn->subTypeInfos[i].second];
            int64_t subAddr = paramAddr + subOffset;
            subTypeOffstack.push_back(i);
            analysisParam(subTn, subAddr, ti, subTypeOffstack);
            subTypeOffstack.pop_back();
        }
        break;
    case NodeType::FUNCTION:
    case NodeType::UNKNOWN:
        break;
    default:
        break;
    }
}

/*
从每个top API出发，下包括多个内部api的执行序列。每个api函数都包含所有参数的描述信息。
每个参数描述信息，包含多个参数描述项。每个参数描述项包含{tnids序列，offset，和data}，用于描述在参数树上的一个叶子节点
 */
void onPrologueEnd_EX(uint64_t rbp, FuncInfo *fi)
{
    ApiTraces.emplace_back();
    TraceInfo *newTraceNode = &ApiTraces.back();
    currentTraceRoot->callees.push_back(newTraceNode);
    newTraceNode->parent = currentTraceRoot;
    newTraceNode->name = fi->name;

    for (size_t i = 0; i < callDepth; i++)
    {
        cerr << "\t";
    }
    cerr << "f: " << fi->name << endl;
    callDepth++;

    vector<uint64_t> subTypeOffstack;
    for (size_t i = 0; i < fi->varInfos.size(); i++)
    {
        VarInfo &vi = fi->varInfos[i];
        ArgInfo ai;
        ai.argIdx = i;
        TypeInfoNode *tn = &TypeInfoMap[vi.typeDescId];
        switch (vi.type)
        {
        case VarType::FORMAL_PARAM:
            analysisParam(tn, rbp + vi.addr, ai, subTypeOffstack);
            break;
        case VarType::LOCAL_VARIABLE:
            SizeMap[rbp + vi.addr] = tn->size;
            break;
        case VarType::STATIC_VARIABLE:
        case VarType::GLOBAL_VARIABLE:
            break;
        default:
            break;
        }

        if (ai.taintBytes != 0)
        {
            newTraceNode->argInfos.push_back(ai);
            //  cerr << "\targ " << vi.name << "\n";
            //  ti.show();
        }
    }
    currentTraceRoot = newTraceNode;
}

void onFunctionEnd_EX(uint64_t rbp, FuncInfo *fi)
{
    callDepth--;
    /*     for (size_t i = 0; i < callDepth; i++)
        {
            cerr << "\t";
        }
        cerr << "f: " << fi->name << " ctr: " << currentTraceRoot->name << " pctr: " << currentTraceRoot->parent->name << " end\n";
        assert(fi->name == currentTraceRoot->name); */

    for (VarInfo &vi : fi->varInfos)
    {
        if (vi.type == VarType::LOCAL_VARIABLE)
        {
            SizeMap.erase(rbp + vi.addr);
        }
    }

    currentTraceRoot = currentTraceRoot->parent;
}

void onMallocBegin(uint64_t size)
{
    pendingSize = size;
}

void onMallocEnd(uint64_t addr)
{
    SizeMap[addr] = pendingSize;
    // fprintf(stderr,"malloc %lu at 0x%lx\n",pendingSize,addr);
}

void onFreeBegin(uint64_t addr)
{
    SizeMap.erase(addr);
    // fprintf(stderr,"free at 0x%lx\n",addr);
}

void onExit(int32_t code, void *v)
{
    /*     if (noAFLmode)
        {
            for (size_t i = 0; i < shm_ptr->itemNum ; i++)
            {
                taintResult *tr = &shm_ptr->items[i];
                fprintf(stderr, "offset:0x%x,hint:%hx,group:%hx\n", tr->offset, tr->hint,tr->groupId);
            }
        } */
    uint32_t hintCount = 0;
    set<uint32_t> coverSet;
    for (size_t i = 0; i < shm_ptr->itemNum; i++)
    {
        taintResult *tr = &shm_ptr->items[i];
        coverSet.insert(tr->offset);
        if (tr->hint <= 0xff)
        {
            hintCount++;
        }
    }
    std::cerr << "write taint result:" << shm_ptr->itemNum << " hint count:" << hintCount << " cover count:"<< coverSet.size() <<"\n";
    exit(0);
}

json handleApiTraceNode(TraceInfo *node)
{
    json jNode;
    json jCallees;
    json jArgInfos;
    jNode["name"] = node->name;
    for (TraceInfo *callee : node->callees)
    {
        jCallees.push_back(handleApiTraceNode(callee));
    }
    jNode["callees"] = jCallees;

    for (ArgInfo &ai : node->argInfos)
    {
        for (size_t i = 0; i < ai.tnid_buf.size(); i++)
        {
            json jArg;
            jArg["idx"] = ai.argIdx;
            vector<uint64_t> &tnids = ai.tnid_buf[i];
            vector<uint64_t> &content_offset_buf = ai.content_buf[i].first;
            stringstream str_tnids;
            for (uint64_t tnid : tnids)
            {
                str_tnids << tnid << ",";
            }
            jArg["tnid"] = str_tnids.str();

            stringstream str_offsets;
            for (uint64_t offset : content_offset_buf)
            {
                str_offsets << offset << ",";
            }
            jArg["offsets"] = str_offsets.str();

            jArg["data"] = ai.content_buf[i].second;
            jArgInfos.push_back(jArg);
        }
    }
    jNode["args"] = jArgInfos;
    return jNode;
}

void onExit_EX(int32_t code, void *v)
{
    json jApiTrace = handleApiTraceNode(&ApiTraces[0]);
    std::ofstream f("tr.json");
    f << jApiTrace;
    f.close();
    exit(0);
}

/*
 *===========================================================================
 *                         Init Related
 *===========================================================================
 */
void str2Vector(vector<uint64_t> &buf, string str)
{
    char *token;
    uint64_t length = str.length();
    char *line = (char *)str.c_str();
    if (line[length - 1] == ',')
        line[length - 1] = 0;

    token = strtok(line, ",");
    while (token)
    {
        buf.push_back(strtoul(token, nullptr, 10));
        token = strtok(NULL, ",");
    }
}

char *hexStr2Data(string hexStr)
{
    char *data = (char *)malloc(hexStr.length() / 2);

    for (size_t i = 0; i < hexStr.length(); i += 2)
    {
        char h = hexStr.c_str()[i];
        char l = hexStr.c_str()[i + 1];
        uint8_t d1 = h <= '9' ? (h - '0') * 16 : (h - 'A' + 10) * 16;
        uint8_t d2 = l <= '9' ? l - '0' : l - 'A' + 10;
        data[i / 2] = d1 + d2;
    }
    return data;
}

TraceInfo *handleJapiTraceNode(json &jNode)
{
    ApiTraces.emplace_back();
    TraceInfo *newNode = &ApiTraces.back();
    newNode->name = jNode["name"];
    newNode->parent = currentTraceRoot;
    newNode->trackIdx = 0;
    newNode->trid = trid++;
    currentTraceRoot = newNode;

    for (json jCallee : jNode["callees"])
    {
        newNode->callees.push_back(handleJapiTraceNode(jCallee));
    }

    std::vector<CompareItem> &cis = newNode->compItems;
    for (json jArg : jNode["args"])
    {
        CompareItem ci;
        ci.argIdx = jArg["idx"];
        str2Vector(ci.tnid_buf, jArg["tnid"]);
        str2Vector(ci.offsets, jArg["offsets"]);
        ci.data = hexStr2Data(jArg["data"]);
        cis.push_back(ci);
    }
    currentTraceRoot = newNode->parent;
    return newNode;
}

void show(TraceInfo *tri)
{
    for (size_t i = 0; i < callDepth; i++)
        cerr << "\t";
    cerr << tri->name << " " << tri->trid << "\n";
    callDepth++;
    for (TraceInfo *sti : tri->callees)
    {
        show(sti);
    }
    callDepth--;
}

bool initTraceInfo()
{
    std::ifstream f(KnobTraceFile.Value());
    if (!f.is_open())
    {
        std::cerr << "open trace file fail\n";
        return false;
    }
    json jApiTrace = json::parse(f);
    handleJapiTraceNode(jApiTrace);
    currentTraceRoot = &ApiTraces[0];
    // show(currentTraceRoot);
    f.close();
    return true;
}

/*
设置每一个函数的end prologue 和每个参数的读取位置
 */

bool initInfoMap(uint64_t loadOffset)
{
    std::ifstream f(KnobExtractFile.Value());
    if (!f.is_open())
    {
        std::cerr << "open ex.json fail\n";
        return false;
    }
    json paramTree = json::parse(f);
    for (auto it : paramTree["FuncDescList"])
    {
        FuncInfo fi;
        fi.name = it["name"];
        fi.prologueEndAddr = it["prologue_end"];
        fi.prologueEndAddr += loadOffset;
        for (auto var : it["vars"])
        {
            string type = var["type"];
            VarInfo vi;
            if (type == "a")
            {
                vi.name = var["name"];
                vi.type = VarType::FORMAL_PARAM;
                vi.typeDescId = var["typeDescID"];
                vi.addr = var["addr"];
            }
            else if (type == "v")
            {
                vi.name = var["name"];
                vi.type = VarType::LOCAL_VARIABLE;
                vi.typeDescId = var["typeDescID"];
                vi.addr = var["addr"];
            }
            else if (type == "s")
            {
                vi.name = var["name"];
                vi.type = VarType::STATIC_VARIABLE;
                vi.typeDescId = var["typeDescID"];
                vi.addr = var["addr"];
                vi.addr += loadOffset;
            }
            else
            {
                assert(false);
            }
            fi.varInfos.push_back(vi);
        }
        FuncInfoMap[fi.name] = fi;
    }

    for (auto var : paramTree["GlobalVars"])
    {
        VarInfo vi;
        vi.name = var["name"];
        vi.type = VarType::GLOBAL_VARIABLE;
        vi.typeDescId = var["typeDescID"];
        vi.addr = var["addr"];
        vi.addr += loadOffset;
        globalVarInfos.push_back(vi);
    }

    for (auto it : paramTree["TypeDescList"])
    {
        TypeInfoNode tn;

        tn.id = it["id"];
        tn.kind = (NodeType)it["type"];
        uint64_t offset, subId;
        switch (tn.kind)
        {
        case NodeType::FLAT:
            tn.size = it["size"];
            break;
        case NodeType::POINTER:
        case NodeType::AGGREGATE:
            tn.size = it["size"];
            for (auto subit : it["subType"])
            {
                offset = subit["offset"];
                subId = subit["subID"];
                tn.subTypeInfos.push_back(std::pair<uint64_t, uint64_t>(offset, subId));
            }
            break;
        case NodeType::FUNCTION:
        case NodeType::UNKNOWN:
            break;
        default:
            break;
        }
        TypeInfoMap[tn.id] = tn;
    }

    f.close();

    for (VarInfo &vi : globalVarInfos)
    {
        TypeInfoNode *tn = &TypeInfoMap[vi.typeDescId];
        SizeMap[vi.addr] = tn->size;
    }
    return true;
}

void traceInst(string *ins)
{
    cerr << "tracing:" << *ins << "\n";
}

void onImgLoad(IMG img, VOID *v)
{
    const string &imgName = IMG_Name(img);
    uint64_t loadOffset = IMG_LoadOffset(img);
    // std::cerr << imgName << "\n";
    if (imgName.find("libpng_uninstr.so") != string::npos)
    {
        initInfoMap(loadOffset);
        for (SEC sec = IMG_SecHead(img); SEC_Valid(sec); sec = SEC_Next(sec))
        {
            // std::cerr << SEC_Name(sec) << "------\n";
            if (SEC_Name(sec) != ".text")
                continue;

            // fprintf(stderr,"inspect %s at 0x%lx ,offset:0x%lx\n",imgName.c_str(),SEC_Address(sec),IMG_LoadOffset(img));
            for (RTN rtn = SEC_RtnHead(sec); RTN_Valid(rtn); rtn = RTN_Next(rtn))
            {
                string funcName = RTN_Name(rtn);
                auto it = FuncInfoMap.find(funcName);
                if (it != FuncInfoMap.end())
                {
                    RTN_Open(rtn);
                    FuncInfo &fi = (*it).second;
                    bool inserted = false;
                    if (KnobIsExtract.Value())
                        RTN_InsertCall(rtn, IPOINT_AFTER, (AFUNPTR)onFunctionEnd_EX, IARG_REG_VALUE, REG_RBP, IARG_PTR, &fi, IARG_END);
                    else
                        RTN_InsertCall(rtn, IPOINT_AFTER, (AFUNPTR)onFunctionEnd, IARG_REG_VALUE, REG_RBP, IARG_PTR, &fi, IARG_END);

                    for (INS ins = RTN_InsHead(rtn); INS_Valid(ins); ins = INS_Next(ins))
                    {
                        uint64_t addr = INS_Address(INS_Next(ins));

                        /*                         if (funcName == "png_crc_finish")
                                                    INS_InsertCall(ins, IPOINT_BEFORE, (AFUNPTR)traceInst, IARG_UINT64,new string(INS_Disassemble(ins)), IARG_END); */

                        if (addr == fi.prologueEndAddr)
                        {
                            if (KnobIsExtract.Value())
                                INS_InsertCall(ins, IPOINT_AFTER, (AFUNPTR)onPrologueEnd_EX, IARG_REG_VALUE, REG_RBP, IARG_PTR, &fi, IARG_END);
                            else
                                INS_InsertCall(ins, IPOINT_AFTER, (AFUNPTR)onPrologueEnd, IARG_REG_VALUE, REG_RBP, IARG_PTR, &fi, IARG_END);
                            inserted = true;
                            break;
                        }
                    }
                    if (!inserted)
                    {
                        fprintf(stderr, "%s is not inserted\n", funcName.c_str());
                        assert(false);
                    }
                    // std::cerr <<"hooking "<<RTN_Name(rtn) << "\n";
                    RTN_Close(rtn);
                }
                else
                {
                    // cerr << "[onImgLoad]: " << RTN_Name(rtn) << " not hooked\n";
                }
            }
        }
    }

    if (imgName == "/lib/x86_64-linux-gnu/libc.so.6")
    {
        RTN rtnM = RTN_FindByName(img, "malloc");
        RTN rtnF = RTN_FindByName(img, "free");
        if (RTN_Valid(rtnM) && RTN_Valid(rtnF))
        {
            RTN_Open(rtnM);
            RTN_InsertCall(rtnM, IPOINT_BEFORE, (AFUNPTR)onMallocBegin, IARG_FUNCARG_ENTRYPOINT_VALUE, 0, IARG_END);
            RTN_InsertCall(rtnM, IPOINT_AFTER, (AFUNPTR)onMallocEnd, IARG_FUNCRET_EXITPOINT_VALUE, IARG_END);
            RTN_Close(rtnM);

            RTN_Open(rtnF);
            RTN_InsertCall(rtnF, IPOINT_BEFORE, (AFUNPTR)onFreeBegin, IARG_FUNCARG_ENTRYPOINT_VALUE, 0, IARG_END);
            RTN_Close(rtnF);
        }
        else
        {
            cerr << "error: can not find malloc and free\n";
        }
    }
}

void onNewThread(THREADID threadIndex, CONTEXT *ctxt, INT32 flags, VOID *v)
{
    if (threadIndex != 0)
    {
        cerr << "error: new thread!\n";
    }
}

void onFork(THREADID threadid, const CONTEXT *ctxt, VOID *v)
{
    cerr << "error: new process!\n";
}

int main(int argc, char **argv)
{
    setbuf(stdout, NULL);
    setbuf(stderr, NULL);
    /* initialize symbol processing */
    PIN_InitSymbols();

    if (unlikely(PIN_Init(argc, argv)))
        return EXIT_FAILURE;

    if (unlikely(libdft_init() != 0))
        return EXIT_FAILURE;

    // init fdinfoMap
    fdInfoMap[STDIN_FILENO] = new fdInfo();
    fdInfoMap[STDIN_FILENO]->fileName = "stdin";

    syscall_set_post(&syscall_desc[__NR_open], post_open_hook);
    syscall_set_post(&syscall_desc[__NR_openat], post_openat_hook);
    syscall_set_post(&syscall_desc[__NR_dup], post_dup_hook);
    syscall_set_post(&syscall_desc[__NR_dup2], post_dup2_hook);
    syscall_set_post(&syscall_desc[__NR_dup3], post_dup2_hook);
    syscall_set_post(&syscall_desc[__NR_close], post_close_hook);

    syscall_set_post(&syscall_desc[__NR_read], post_read_hook);
    syscall_set_post(&syscall_desc[__NR_pread64], post_pread64_hook);
    syscall_set_post(&syscall_desc[__NR_readv], post_readv_hook);
    // syscall_set_post(&syscall_desc[__NR_mmap], post_mmap_hook);

    ApiTraces.reserve(5000);
    if (!KnobIsExtract.Value())
    {
        int shm_id = shmget((key_t)40446, 1U << 16, 0600);
        if (shm_id < 0)
        {
            shm_ptr = (taintResultInfo *)malloc(1U << 16);
            noAFLmode = true;
            cerr << "no afl-fuzz mode\n";
        }
        else
        {
            shm_ptr = (taintResultInfo *)shmat(shm_id, NULL, 0);
            if (shm_ptr == (void *)-1)
            {
                cerr << "shmat fail\n";
                return 1;
            }
        }
        shm_ptr->itemNum = 0;
        PIN_AddFiniFunction(onExit, 0);
        initTraceInfo();
    }
    else
    {
        ApiTraces.emplace_back();
        currentTraceRoot = &(*ApiTraces.begin());
        currentTraceRoot->name = "__top";
        PIN_AddFiniFunction(onExit_EX, 0);
    }

    IMG_AddInstrumentFunction(onImgLoad, 0);
    PIN_AddThreadStartFunction(onNewThread, 0);
    PIN_AddForkFunction(FPOINT_BEFORE, onFork, 0);

    PIN_StartProgram();

    /* typically not reached; make the compiler happy */
    return EXIT_SUCCESS;
}

/* void onExit2(int32_t code, void *v)
{
    cerr << "\n\n\n\n================summary================";
    for (auto &item : FuncInfoMap)
    {
        FuncInfo &fi = item.second;
        uint64_t taintBytes = 0;
        for (VarInfo &vi : fi.varInfos)
            taintBytes += vi.ti.taintBytes;

        if (taintBytes == 0)
            continue;

        cerr << fi.name << endl;
        for (VarInfo &vi : fi.varInfos)
        {
            ArgInfo &ti = vi.ti;
            if (ti.taintBytes == 0)
                continue;

            cerr << "\targ " << vi.name << " tainted bytes:" << taintBytes << " ";
            cerr << "{";
            auto it = ti.offset_buf.begin();
            while (it != ti.offset_buf.end())
            {
                cerr << " " << *it;
                it++;
            }
            cerr << " }\n";
        }
    }
}

void onExit(int32_t code, void *v)
{
    for (auto &item : FuncInfoMap)
    {
        FuncInfo &fi = item.second;
        uint64_t taintBytes = 0;
        for (VarInfo &vi : fi.varInfos)
            taintBytes += vi.ti.taintBytes;

        if (taintBytes == 0)
            continue;

        cerr << fi.name << endl;
        for (VarInfo &vi : fi.varInfos)
        {
            ArgInfo &ti = vi.ti;
            if (ti.taintBytes == 0)
                continue;

            cerr << "\targ " << vi.name << " tainted bytes:" << taintBytes << " ";
            cerr << "{";
            auto it = ti.offset_buf.begin();
            uint64_t start_offset = *it;
            uint64_t last_offset = *it;
            fdInfo *last_fdInfo = getFdInfo(last_offset);
            it++;

            while (it != ti.offset_buf.end())
            {
                uint64_t curr_offset = *it;
                fdInfo *curr_fdInfo = getFdInfo(curr_offset);
                if (curr_offset == last_offset + 1 && curr_fdInfo == last_fdInfo)
                {
                    last_offset = curr_offset;
                    it++;
                    continue;
                }

                // 分段条件已经满足
                uint64_t last_file_start = last_fdInfo->getFileOffset(start_offset);
                uint64_t last_file_end = last_file_start + last_offset - start_offset;
                fprintf(stderr, "[%s:%lu-%lu]", last_fdInfo->fileName.c_str(), last_file_start, last_file_end);

                start_offset = curr_offset;
                last_offset = curr_offset;
                last_fdInfo = curr_fdInfo;
                it++;
            }
            cerr << " }\n";
        }
    }
} */

/*
Dwarf_Unsigned size = getDieTypeSize(dbg, param_die);
if (size > 8)
{
    cerr << "multi reg pass: " << size << "\n";
    assert(size % 8 == 0);
}

for (size_t i = 0; i < size; i += 8)
{
    assert(!regStack.empty());
    // offset小于0表明该参数通过reg发送，其addrOffset为
    //  |1--------------|regIdx|regOffset|
    //  |------48bit----|-8bit-|---8bit--|
    int64_t addrOffset = 0;
    addrOffset |= (uint64_t)1 << 63;    // 设置符号
    addrOffset |= regStack.back() << 8; // 设置reg编号,offset默认为0
    regStack.pop_back();
    FuncInfoMap[funcName].argOffsets.push_back(addrOffset);
}
Dwarf_Unsigned getDieTypeSize(Dwarf_Debug dbg, Dwarf_Die die)
{
    Dwarf_Error err;
    Dwarf_Attribute attr;
    Dwarf_Off offset;
    Dwarf_Die typedie;
    Dwarf_Unsigned size;
    Dwarf_Half tag;

    dwarf_tag(die, &tag, &err);
    switch (tag)
    {
    case DW_TAG_formal_parameter:
    case DW_TAG_typedef:
    case DW_TAG_restrict_type:
        dwarf_attr(die, DW_AT_type, &attr, &err);
        dwarf_global_formref(attr, &offset, &err);
        dwarf_offdie_b(dbg, offset, 1, &typedie, &err);
        return getDieTypeSize(dbg, typedie);
        break;
    case DW_TAG_pointer_type:
        return 8;
    case DW_TAG_base_type:
    case DW_TAG_structure_type:
        assert(dwarf_bytesize(die, &size, &err) == DW_DLV_OK);
        return size;

    default:
        printf("error : unhandled tag type:%hu\n", tag);
    }

    return 0;
}

bool initInfoMap(uint64_t loadOffset)
{
    FILE *fd = fopen("ex.txt", "r");
    if (fd == nullptr)
    {
        std::cerr << "open ex.txt fail\n";
        return false;
    }
    char *line = NULL;
    uint64_t len = 0;
    int nread;
    FuncInfo *currentFI = nullptr;
    while ((nread = getline(&line, &len, fd)) != -1)
    {
        char *token;
        if (line[nread - 1] == '\n')
            line[nread - 1] = 0;

        token = strtok(line, ":");
        std::vector<std::string> tokens;
        while (token)
        {
            tokens.push_back(token);
            token = strtok(NULL, ":");
        }
        if (tokens[0] == "f")
        {
            FuncInfo fi;
            fi.name = tokens[1];
            fi.prologueEndAddr = strtoul(tokens[2].c_str(), nullptr, 10) + loadOffset;
            fi.inst_id = strtoul(tokens[3].c_str(), nullptr, 10);
            FuncInfoMap[fi.name] = fi;
            currentFI = &FuncInfoMap[fi.name];
        }
        else if (tokens[0] == "a")
        {
            VarInfo vi;
            vi.name = tokens[1];
            vi.type = VarType::FORMAL_PARAM;
            vi.typeDescId = strtoul(tokens[2].c_str(), nullptr, 10);
            vi.addr = strtol(tokens[3].c_str(), nullptr, 10);
            currentFI->varInfos.push_back(vi);
        }
        else if (tokens[0] == "v")
        {
            VarInfo vi;
            vi.name = tokens[1];
            vi.type = VarType::LOCAL_VARIABLE;
            vi.typeDescId = strtoul(tokens[2].c_str(), nullptr, 10);
            vi.addr = strtol(tokens[3].c_str(), nullptr, 10);
            currentFI->varInfos.push_back(vi);
        }
        else if (tokens[0] == "s")
        {
            VarInfo vi;
            vi.name = tokens[1];
            vi.type = VarType::STATIC_VARIABLE;
            vi.typeDescId = strtoul(tokens[2].c_str(), nullptr, 10);
            vi.addr = strtol(tokens[3].c_str(), nullptr, 10) + loadOffset;
            currentFI->varInfos.push_back(vi);
        }
        else if (tokens[0] == "g")
        {
            VarInfo vi;
            vi.name = tokens[1];
            vi.type = VarType::GLOBAL_VARIABLE;
            vi.typeDescId = strtoul(tokens[2].c_str(), nullptr, 10);
            vi.addr = strtol(tokens[3].c_str(), nullptr, 10) + loadOffset;
            globalVarInfos.push_back(vi);
        }
        else if (tokens[0] == "t")
        {
            TypeInfoNode tn;
            tn.id = strtoull(tokens[1].c_str(), nullptr, 10);
            tn.kind = (NodeType)strtoull(tokens[2].c_str(), nullptr, 10);
            uint64_t offset, subId;
            switch (tn.kind)
            {
            case NodeType::FLAT:
                tn.size = strtoull(tokens[3].c_str(), nullptr, 10);
                break;
            case NodeType::POINTER:
                tn.size = strtoull(tokens[3].c_str(), nullptr, 10);
                offset = 0;
                subId = strtoull(tokens[5].c_str(), nullptr, 10);
                tn.subTypeInfos.push_back(std::pair<uint64_t, uint64_t>(offset, subId));
                break;
            case NodeType::AGGREGATE:
                tn.size = strtoull(tokens[3].c_str(), nullptr, 10);
                for (size_t i = 4; i < tokens.size(); i += 2)
                {
                    offset = strtoull(tokens[i].c_str(), nullptr, 10);
                    subId = strtoull(tokens[i + 1].c_str(), nullptr, 10);
                    tn.subTypeInfos.push_back(std::pair<uint64_t, uint64_t>(offset, subId));
                }
                break;
            case NodeType::FUNCTION:
            case NodeType::UNKNOWN:
                break;
            default:
                break;
            }
            TypeInfoMap[tn.id] = tn;
        }
    }
    fclose(fd);

    for (VarInfo &vi : globalVarInfos)
    {
        TypeInfoNode *tn = &TypeInfoMap[vi.typeDescId];
        SizeMap[vi.addr] = tn->size;
    }
    return true;
}

*/