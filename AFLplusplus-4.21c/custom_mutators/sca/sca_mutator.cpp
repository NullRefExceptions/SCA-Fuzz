/*
  New Custom Mutator for AFL++
  Written by Khaled Yakdan <yakdan@code-intelligence.de>
             Andrea Fioraldi <andreafioraldi@gmail.com>
             Shengtuo Hu <h1994st@gmail.com>
             Dominik Maier <mail@dmnk.co>
*/

// You need to use -I/path/to/AFLplusplus/include -I.
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <stdio.h>
#include <string>
#include <sstream>
#include <iostream>
#include <mqueue.h>
#include <vector>
#include <filesystem>

extern "C" {
#include "afl-fuzz.h"
#include "afl-mutations.h"
}

using namespace std;

#define CMD_NOP 2
#define CMD_EXEC 1
#define CMD_EXIT 0

struct exec_cmd {
  int  op;
  char cmd[1500];
};

struct taintResult {
  uint32_t offset;
  uint16_t hint;
  uint16_t groupId;
};

struct taintResultInfo {
  uint32_t    itemNum;
  taintResult items[];
};

struct my_mutator {
  afl_state_t *afl;
  // any additional data here!
  int                 shm_id;
  taintResultInfo    *tr_ptr;
  uint32_t            taintResultIdx;
  vector<taintResult> taintResults;
  vector<string> handledItem;
  uint64_t            shm_size;
  char               *exFile;
  char               *trFile;
  u8                 *mutated_out;
  u8                 *havoc_buf;
  mqd_t               mq;
  bool dtaInPlace;  //有些程序会修改输入，从而导致queue文件损坏，因此DTA需要在新产生的副本上运行
};

extern "C" my_mutator *afl_custom_init(afl_state_t *afl, unsigned int seed) {
  my_mutator *data = new my_mutator();
  data->mutated_out = (u8 *)malloc(MAX_FILE);
  data->havoc_buf = (u8 *)malloc(MAX_FILE);
  data->afl = afl;
  data->shm_id =
      shmget((key_t)40446, MAP_SIZE, IPC_CREAT | IPC_EXCL | DEFAULT_PERMISSION);
  if (data->shm_id < 0) { PFATAL("shmget() failed"); }
  data->tr_ptr = (taintResultInfo *)shmat(data->shm_id, NULL, 0);
  if (data->tr_ptr == (void *)-1) { shmctl(data->shm_id, IPC_RMID, NULL); }
  data->exFile = getenv("exFile");
  data->trFile = getenv("trFile");
  if (data->exFile == NULL || data->trFile == NULL) {
    PFATAL("exFile or trFile not set");
  }
  
  data->dtaInPlace = getenv("dtaInPlace")!=NULL;
  data->mq = mq_open("/sca_mq", O_WRONLY);
  if (data->mq == (mqd_t)-1) { PFATAL("fail open mq"); }
  data->taintResultIdx = 0;
  return data;
}

extern "C" size_t afl_custom_fuzz(my_mutator *data, uint8_t *buf,
                                  size_t buf_size, u8 **out_buf,
                                  uint8_t *add_buf, size_t add_buf_size,
                                  size_t max_size) {
  memcpy(data->mutated_out, buf, buf_size);
  *out_buf = data->mutated_out;
  if (data->taintResultIdx >= data->taintResults.size())
  {
    data->taintResultIdx = 0;
  }
  
  // 搜索当前dta块
  while (data->taintResultIdx < data->taintResults.size()) {
    uint16_t curr_groupId = data->taintResults[data->taintResultIdx].groupId;
    bool     writen = false;
    // 搜索在一个group中的结果
    for (; data->taintResultIdx < data->taintResults.size();
         data->taintResultIdx++) {
      taintResult *tr = &data->taintResults[data->taintResultIdx];

      // 当前group分析完毕
      if (tr->groupId != curr_groupId) break;

      if (tr->hint <= 0xff) {
        data->mutated_out[tr->offset] = tr->hint;
        writen = true;
      }
    }
    if (writen) { return buf_size; }
  }
  return 0;
  //
}

extern "C" uint8_t afl_custom_queue_new_entry(
    my_mutator *data, const uint8_t *filename_new_queue,
    const uint8_t *filename_orig_queue) {
  if (filename_orig_queue == nullptr)
  {
    return 0;
  }
  
  string name((char *)filename_orig_queue);
  for(string &s:data->handledItem)
  {
    if (s == name)
      return 0;
  }
  data->handledItem.push_back(name);
  
  
  if (data->dtaInPlace)
  {
    filesystem::path oldPath(name);
    filesystem::path tmp("/tmp");
    tmp /= oldPath.filename();
    copy(oldPath,tmp,filesystem::copy_options::overwrite_existing);
    name = tmp.string();
  }
  

  exec_cmd cm;
  memset(&cm, 0, sizeof(exec_cmd));
  std::stringstream cmd;
  cmd << "GLIBC_TUNABLES=glibc.cpu.hwcaps=-AVX,-AVX2,-AVX512BW,-AVX512DQ,-"
         "AVX512F,-AVX512VL,-BMI1,-BMI2,-LZCNT,-MOVBE,-RTM,-SSE4_1,-SSE4_2,-"
         "SSSE3,-SSE2,-SSE ";
  cmd << "LD_LIBRARY_PATH=/root/instrument/targets/libpng "
         "LD_PRELOAD=libpng_uninstr.so ";
  cmd << "/usr/local/bin/pin -t "
         "/root/instrument/libdft_ECT/tools/obj-intel64/extract.so ";
  cmd << "-ex 0 ";
  cmd << "-exFile " << data->exFile << " ";
  cmd << "-trFile " << data->trFile << " ";
  cmd << "-- ";
  char **arg = data->afl->argv;
  if (arg == nullptr) { return 0; }

  while (*arg) {
    if (strstr(*arg, ".cur_input") != NULL)
      cmd << name << " ";
    else
      cmd << *arg << " ";

    arg++;
  }
  // cmd << ">/dev/null 2>/dev/null";
  //std::cerr << cmd.str();
  memcpy(cm.cmd, cmd.str().c_str(), cmd.str().size());
  cm.op = CMD_EXEC;
  int res = mq_send(data->mq, (char *)&cm, sizeof(exec_cmd), 0);
  cm.op = CMD_NOP;
  res = mq_send(data->mq, (char *)&cm, sizeof(exec_cmd), 0);
  res = mq_send(data->mq, (char *)&cm, sizeof(exec_cmd), 0);
  // return 0;
  // 不知道为什么system调起的pin执行速度极慢，我们这里将命令发送到exec
  // server执行 system(cmd.str().c_str());
  MEM_BARRIER();
  if (data->tr_ptr->itemNum != 0) {
    for (uint32_t i = 0; i < data->tr_ptr->itemNum; i++) {
      taintResult *tr = &data->tr_ptr->items[i];
      bool         exist = false;
      if (tr->hint > 0xff) continue;
      for (taintResult &otr : data->taintResults) {
        if (tr->hint == otr.hint &&
            tr->offset == otr.offset) {
          exist = true;
          break;
        }
      }
      if (!exist) { data->taintResults.push_back(*tr); }
    }
  }

  return 0;
}

extern "C" void afl_custom_deinit(my_mutator *data) {
  exec_cmd cm;
  cm.op = CMD_EXIT;
  mq_send(data->mq, (char *)&cm, sizeof(exec_cmd), 0);
  shmdt(data->tr_ptr);
  shmctl(data->shm_id, IPC_RMID, NULL);
  free(data->mutated_out);
  free(data->havoc_buf);
  free(data);
}

extern "C" void afl_custom_splice_optout(my_mutator *data) {
  (void)(data);
}
