#pragma once

#include "sys/system.h"
#include "fdsched/scheduler.h"

#define MAX_INPUT_CHANNELS 16

//@rc::import fdsched_extra from refinedc.examples.scheduler.src.fdsched

/* state of the non-preemptive fixed-priority scheduler */
struct
[[rc::refined_by("fd_scheduler : fd_sched")]]
[[rc::typedef("fd_t : ...")]]
fd_scheduler {
  /* the file descriptors we monitor */
    [[rc::field("array_p<i32,{input_channels fd_scheduler `at_type` (int i32)},"
		"{16%nat - (length (input_channels fd_scheduler))}>")]]
  int input_channels[MAX_INPUT_CHANNELS];
  [[rc::field("{length (input_channels fd_scheduler)} @ int<u64>")]]
  nfds_t num_channels;

  /* the NP-FP scheduler */
  [[rc::field("{sched_state fd_scheduler} @ npfp_t")]]
  struct npfp_scheduler sched;
};


void fds_init(struct fd_scheduler* fds);
int fds_add_channel(struct fd_scheduler* fds, int fd);
void fds_set_callback(struct fd_scheduler* fds,
                     message_type_t type, callback_fn_t f, priority_t prio);
int fds_run(struct fd_scheduler* fds);
