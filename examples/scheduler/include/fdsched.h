#pragma once

#include "sys/system.h"
#include "fdsched/scheduler.h"

#define MAX_INPUT_CHANNELS 16

/* state of the non-preemptive fixed-priority scheduler */
struct fd_scheduler {
  /* the file descriptors we monitor */
  struct pollfd input_channels[MAX_INPUT_CHANNELS];
  nfds_t num_channels;

  /* the NP-FP scheduler */
  struct npfp_scheduler sched;
};


void fds_init(struct fd_scheduler* fds);
int fds_add_channel(struct fd_scheduler* fds, int fd);
void fds_set_callback(struct fd_scheduler* fds,
                     message_type_t type, callback_fn_t f, priority_t prio);
int fds_run(struct fd_scheduler* fds);
