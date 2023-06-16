#pragma once

#include "fdsched/message.h"
#include "fdsched/priority.h"

typedef int (*callback_fn_t)(struct message *);

struct callback {
  priority_t prio;
  callback_fn_t f;
};

/* state of the non-preemptive fixed-priority scheduler */
struct npfp_scheduler {
  /* the registered callbacks */
  struct callback callbacks[NUM_MESSAGE_TYPES];

  /* pending callback activations */
  struct message_queue pending[NUM_PRIORITIES];

  /* which priority levels are non-empty? */
  prio_bitmap_t prio_levels;
};

static inline
void npfp_enqueue(struct npfp_scheduler *sched, struct message* msg) {
  /* identify the type of message we're looking at */
  msg->type = message_identify_type(msg);
  /* look up the fixed priority of such messages */
  priority_t msg_prio = sched->callbacks[msg->type].prio;
  /* add it to the appropriate queue */
  message_queue_add(&sched->pending[msg_prio], msg);
  /* note that the queue isn't empty anymore */
  priority_level_set(&sched->prio_levels, msg_prio);
}

static inline
struct message* npfp_dequeue(struct npfp_scheduler *sched) {
  /* figure out top pending priority level */
  int top_prio = highest_pending_priority(&sched->prio_levels);
  if (priority_search_none_found(top_prio))
    return NULL;
  else {
    /* dequeue the highest-priority message */
    struct message *msg = message_queue_remove(&sched->pending[top_prio]);

    /* check if we have to clear the priority bit */
    if (message_queue_empty(&sched->pending[top_prio])) {
      /* note that the queue is now empty */
      priority_level_clear(&sched->prio_levels, top_prio);
    }

    return msg;
  }
}

static inline
int npfp_dispatch(struct npfp_scheduler *sched, struct message *msg) {
  return sched->callbacks[msg->type].f(msg);
}

