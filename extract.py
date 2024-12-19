import sys
import json
from elftools.elf.elffile import ELFFile
from elftools.dwarf.compileunit import CompileUnit, DIE
from elftools.dwarf.enums import *
from elftools.dwarf.locationlists import LocationParser, LocationExpr
from elftools.dwarf.dwarf_expr import DWARFExprParser
from elftools.dwarf.descriptions import *
from elftools.dwarf.dwarfinfo import DWARFInfo
from elftools.dwarf.lineprogram import LineProgram, LineProgramEntry, LineState
from collections import namedtuple


forward_types = ["DW_TAG_atomic_type",
                 "DW_TAG_const_type",
                 "DW_TAG_immutable_type",
                 "DW_TAG_packed_type",
                 "DW_TAG_restrict_type",
                 "DW_TAG_shared_type",
                 "DW_TAG_volatile_type",
                 "DW_TAG_typedef"]

skip_types = ["DW_TAG_subroutine_type"]

FLAT = 0x0  # 基本类型和子元素均为FLAT类型的结构体类型
POINTER = 0x1  # 指针类型，被指对象在subType中(注意可能是数组)
AGGREGATE = 0x2  # 聚合类型，各个子字段在subType中
FUNCTION = 0x3  # 函数类型
UNKNOWN = 0x4  # 未知类型


class TypeDesc():
    def __init__(self) -> None:
        self.id = 0
        self.size = -1  # byte counts, -1 means unknown
        self.type = UNKNOWN
        self.subTypeDescs = []
        self.die: DIE = None


class VarDesc():
    def __init__(self) -> None:
        self.id = 0
        self.name = ""
        self.isFormalParam = False
        self.isLocal = True
        self.typeDescID = 0
        self.addr = 0


class FuncDesc():
    def __init__(self) -> None:
        self.name = ""
        self.low = 0
        self.high = 0
        self.prologue_end = 0
        self.variables: list[VarDesc] = []


typeDescCount = 0
DieToTypeDescID = {}
IDToTypeDesc: dict[int, TypeDesc] = {}

varDescCount = 0
FuncDescList: list[FuncDesc] = []
GlobalVars: list[VarDesc] = []

# 设置void 类型


def initTypeDesc():
    global typeDescCount
    td = TypeDesc()
    td.size = 1
    td.id = typeDescCount
    td.type = UNKNOWN
    IDToTypeDesc[td.id] = td
    typeDescCount += 1


def getTypeDescID(die: DIE):
    if die.tag in forward_types:
        if "DW_AT_type" in die.attributes:
            return getTypeDescID(die.get_DIE_from_attribute("DW_AT_type"))
        else:
            # 在forwardtype中，可能type属性不存在，这可能代表其forward到了void类型
            return 0  # type id of void

    if die in DieToTypeDescID:
        return DieToTypeDescID[die]

    global typeDescCount
    td = TypeDesc()
    td.id = typeDescCount
    DieToTypeDescID[die] = typeDescCount
    typeDescCount += 1
    td.die = die

    # print(die)

    if die.tag == "DW_TAG_pointer_type":
        td.type = POINTER
        td.size = 8
        if "DW_AT_type" in die.attributes:
            subId = getTypeDescID(die.get_DIE_from_attribute("DW_AT_type"))
        else:
            # void* 类型，导致不存在子类型
            subId = 0  # void
        td.subTypeDescs.append((0, subId))
    elif die.tag == "DW_TAG_array_type":
        subId = getTypeDescID(die.get_DIE_from_attribute("DW_AT_type"))
        subDie = IDToTypeDesc[subId]
        offset = 0
        if subDie.type != UNKNOWN:
            td.type = AGGREGATE
            allCounted = True
            rangeDie: DIE
            for rangeDie in die.iter_children():
                if "DW_AT_count" not in rangeDie.attributes:
                    allCounted = False
                    break

                for i in range(rangeDie.attributes["DW_AT_count"].value):
                    td.subTypeDescs.append((offset, subId))
                    offset += subDie.size

            if allCounted:
                td.size = len(td.subTypeDescs) * subDie.size
            else:
                td.size = -1  # 需要根据运行时信息判断大小
        else:
            # 如果元素类型都不知道，即使在运行时知道大小也没用
            print("warning:array element type unknown, set array type to unknown")
            td.type = UNKNOWN

    elif die.tag == "DW_TAG_structure_type":
        if not die.has_children:
            # 透明定义的结构体
            td.type = UNKNOWN
        else:
            td.type = AGGREGATE
            td.size = die.attributes["DW_AT_byte_size"].value
            count = 0
            subDie: DIE
            for subDie in die.iter_children():
                count += 1
                offset = subDie.attributes["DW_AT_data_member_location"].value
                subId = getTypeDescID(
                    subDie.get_DIE_from_attribute("DW_AT_type"))
                td.subTypeDescs.append((offset, subId))

    elif die.tag == "DW_TAG_base_type":
        td.type = FLAT
        td.size = die.attributes["DW_AT_byte_size"].value

    elif die.tag == "DW_TAG_subroutine_type":
        td.type = FUNCTION

    else:
        print("error: unhandled type: {}".format(die.tag))
        exit()

    IDToTypeDesc[td.id] = td
    return td.id


def processCU(cu: CompileUnit, dwarfinfo: DWARFInfo):
    global varDescCount
    entry: LineProgramEntry
    prologueEnds = []
    for entry in dwarfinfo.line_program_for_CU(cu).get_entries():
        state: LineState = entry.state
        if state == None:
            continue

        if state.prologue_end:
            prologueEnds.append(state.address)

    cuDie = cu.get_top_DIE()
    if not cuDie.has_children:
        return

    if "afl-compiler-rt.o.c" in cuDie.attributes['DW_AT_name'].value.decode():
        return

    location_parser = LocationParser(dwarfinfo.location_lists())
    exp_parser = DWARFExprParser(cu.structs)
    die: DIE
    for die in cuDie.iter_children():
        if die.tag == "DW_TAG_subprogram":
            funcName:str = die.attributes['DW_AT_name'].value.decode()

            # not our target
            if funcName.startswith("magma_"):
                continue
            
            lowAddr = die.attributes['DW_AT_low_pc'].value
            highAddr = die.attributes['DW_AT_high_pc'].value
            prologue_end = 0
            for i in prologueEnds:
                if i > lowAddr and i < lowAddr+highAddr:
                    prologue_end = i
            assert (prologue_end != 0)

            fd = FuncDesc()
            fd.name = funcName
            fd.low = lowAddr
            fd.high = highAddr
            fd.prologue_end = prologue_end

            frame_base = exp_parser.parse_expr(
                die.attributes['DW_AT_frame_base'].value)
            assert (frame_base[0].op_name == "DW_OP_reg6")
            # print(die.attributes['DW_AT_name'].value)
            # print(die.attributes['DW_AT_name'].value)
            varDie: DIE
            for varDie in die.iter_children():
                if varDie.tag == "DW_TAG_formal_parameter" or varDie.tag == "DW_TAG_variable":
                    vd = VarDesc()
                    vd.id = varDescCount
                    varDescCount += 1
                    vd.name = varDie.attributes['DW_AT_name'].value.decode()
                    vd.isFormalParam = varDie.tag == "DW_TAG_formal_parameter"
                    vd.typeDescID = getTypeDescID(
                        varDie.get_DIE_from_attribute("DW_AT_type"))
                    lo = location_parser.parse_from_attribute(
                        varDie.attributes['DW_AT_location'], cu['version'])
                    if isinstance(lo, LocationExpr):
                        expList = exp_parser.parse_expr(lo.loc_expr)
                        assert (len(expList) == 1)
                        if expList[0].op_name == 'DW_OP_fbreg':
                            assert (len(expList[0].args) == 1)
                            vd.isLocal = True
                            vd.addr = expList[0].args[0]
                            fd.variables.append(vd)
                        elif expList[0].op_name == 'DW_OP_addrx':
                            assert (len(expList[0].args) == 1)
                            vd.isLocal = False
                            vd.addr = dwarfinfo.get_addr(
                                cu, expList[0].args[0])
                            fd.variables.append(vd)
                        else:
                            print('unsupported op:{}' % expList[0])
                            exit()

                    else:
                        print("error: unsupported location entry type")
                        exit()

            FuncDescList.append(fd)
        elif die.tag == "DW_TAG_variable":
            vd = VarDesc()
            vd.id = varDescCount
            varDescCount += 1
            vd.name = die.attributes['DW_AT_name'].value.decode()
            vd.typeDescID = getTypeDescID(
                die.get_DIE_from_attribute("DW_AT_type"))
            lo = location_parser.parse_from_attribute(
                die.attributes['DW_AT_location'], cu['version'])
            if isinstance(lo, LocationExpr):
                expList = exp_parser.parse_expr(lo.loc_expr)
                assert (len(expList) == 1)
                if expList[0].op_name == 'DW_OP_addrx':
                    assert (len(expList[0].args) == 1)
                    vd.isLocal = False
                    vd.addr = dwarfinfo.get_addr(cu, expList[0].args[0])
                    GlobalVars.append(vd)
                else:
                    print('unsupported op:{}'.format(expList[0]))
                    exit()

            else:
                print("error: unsupported location entry type")
                exit()
        elif str(die.tag).find("type") != -1:
            continue
        else:
            print("warning: unhandled tag type {}".format(die.tag))
            exit()


def debugDump():
    # dumpFuncDesc and VarDesc
    for fd in FuncDescList:
        print("f:{},low:{},high:{},prologue_end:{}".format(
            fd.name, fd.low, fd.high, fd.prologue_end))  # f 代表函数
        for var in fd.variables:
            if var.isFormalParam:
                assert (var.isLocal)
                print("a:{},tdid:{},addr:rbp+{}".format(var.name,
                      var.typeDescID, var.addr))  # a 代表函数内形参变量
            else:
                if var.isLocal:
                    print("v:{},tdid:{},addr:rsp+{}".format(var.name,
                                                            var.typeDescID, var.addr))  # v 代表函数内的非形参且非static变量
                else:
                    print("s:{},tdid:{},addr:{}".format(
                        var.name, var.typeDescID, var.addr))  # s 代表函数内的static变量

    for var in GlobalVars:
        print("g:{},tdid:{},addr:{}".format(
            var.name, var.typeDescID, var.addr))  # g 代表全局变量

    # dumpTypeDesc
    for k, v in IDToTypeDesc.items():
        if v.die != None:
            offset = v.die.offset
        else:
            offset = -1
        print("t id:{} type:{} size:{} die:{}".format(
            v.id, v.type, v.size, hex(offset)), end="")  # t 代表类型定义
        for (offset, subID) in v.subTypeDescs:
            print(":{}-{}".format(offset, subID), end="")
        print("")


def dump():
    print("m:changeme")
    # dumpFuncDesc and VarDesc
    for fd in FuncDescList:
        print("f:{}:{}".format(
            fd.name, fd.prologue_end))  # f 代表函数
        for var in fd.variables:
            if var.isFormalParam:
                assert (var.isLocal)
                print("a:{}:{}:{}".format(var.name,
                      var.typeDescID, var.addr))  # a 代表函数内形参变量
            else:
                if var.isLocal:
                    print("v:{}:{}:{}".format(var.name,
                                              var.typeDescID, var.addr))  # v 代表函数内的非形参且非static变量
                else:
                    print("s:{}:{}:{}".format(
                        var.name, var.typeDescID, var.addr))  # s 代表函数内的static变量

    for var in GlobalVars:
        print("g:{}:{}:{}".format(var.name, var.typeDescID, var.addr))  # g 代表全局变量

    # dumpTypeDesc
    for k, v in IDToTypeDesc.items():
        print("t:{}:{}:{}".format(v.id, v.type, v.size), end="")  # t 代表类型定义
        for (offset, subID) in v.subTypeDescs:
            print(":{}:{}".format(offset, subID), end="")
        print("")

def dumpJson():
    res = {}
    res["moduleName"] = "/usr/local/lib/libpng16.so.16"
    res["FuncDescList"] = []
    res["GlobalVars"] = []
    res["TypeDescList"] = []
    # dumpFuncDesc and VarDesc
    for fd in FuncDescList:
        fdDes = {}
        fdDes["name"] = fd.name
        fdDes["prologue_end"] = fd.prologue_end
        fdDes["vars"] = []
        for var in fd.variables:
            varDes = {}
            varDes["name"] = var.name
            varDes["typeDescID"] = var.typeDescID
            varDes["addr"] = var.addr
            if var.isFormalParam:
                assert (var.isLocal)
                varDes["type"] = "a" # a 代表函数内形参变量
            else:
                if var.isLocal:
                    varDes["type"] = "v" # v 代表函数内的非形参且非static变量
                else:
                    varDes["type"] = "s" # s 代表函数内的static变量
            fdDes["vars"].append(varDes)
        res["FuncDescList"].append(fdDes)

    for var in GlobalVars:
        varDes = {}
        varDes["name"] = var.name
        varDes["typeDescID"] = var.typeDescID
        varDes["addr"] = var.addr
        res["GlobalVars"].append(varDes)

    # dumpTypeDesc
    for k, v in IDToTypeDesc.items():
        tdes = {}
        tdes["id"] = v.id
        tdes["type"] = v.type
        tdes["size"] = v.size
        tdes["subType"] = []
        for (offset, subID) in v.subTypeDescs:
            tsubDes = {}
            tsubDes["offset"] = offset
            tsubDes["subID"] = subID
            tdes["subType"].append(tsubDes)
        res["TypeDescList"].append(tdes)
    print(json.dumps(res))

def main():
    if len(sys.argv) < 2:
        print("extract.py <file name>")
        return
    filename = sys.argv[1]

    with open(filename, 'rb') as f:
        elffile = ELFFile(f)

        if not elffile.has_dwarf_info():
            print('file has no DWARF info!')
            return

        initTypeDesc()
        dwarfInfo = elffile.get_dwarf_info()
        for cu in dwarfInfo.iter_CUs():
            processCU(cu, dwarfInfo)
            # return

    #dump()
    #debugDump()
    dumpJson()


if __name__ == '__main__':
    main()
