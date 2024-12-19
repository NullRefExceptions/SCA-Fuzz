#include <stdlib.h>
#include <sys/stat.h>
#include <stdio.h>
#include <stdint.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <mqueue.h>
#include <errno.h>
#include <time.h>

#define CMD_NOP   2
#define CMD_EXEC  1
#define CMD_EXIT  0

struct exec_cmd {
  int  op;
  char cmd[1500];
};

struct mq_attr ma;

int main() {
  uint64_t exec_time = 0;
  ma.mq_maxmsg = 1;
  ma.mq_msgsize = sizeof(struct exec_cmd);
  mq_unlink("/sca_mq");
  mqd_t mq = mq_open("/sca_mq", O_CREAT|O_RDONLY, 0666, &ma);
  if (mq == (mqd_t)-1) {
    fprintf(stderr, "fail open mq");
    return -1;
  }
  struct exec_cmd cmd;
  do {
    mq_receive(mq, (char *)&cmd, sizeof(struct exec_cmd), NULL);
    if (cmd.op == CMD_EXEC) {
      //fprintf(stderr,"execute cmd:%s\n",cmd.cmd);
      time_t before = time(0);
      system(cmd.cmd);
      exec_time += time(0)- before;
    } else if (cmd.op == CMD_EXIT) {
      break;
    } else if(cmd.op == CMD_NOP)
    {
      continue;
    }

  } while (1);
  printf("exec server exit,total exec time:%lu\n",exec_time);
  mq_unlink("/sca_mq");
  return 0;
}

//ipcs
//ipcrm -m 