#include <assert.h>
#include <errno.h>
#include <stdlib.h>

#include "sys/system.h"
#include "fdsched.h"

#include "fcntl_specs.h"

[[rc::parameters("msg : {message_data}", "q : loc")]]
[[rc::args("&own<msg @ message<uninit<void*>>>")]]
[[rc::returns("int<i32>")]]
static
int nop_callback(struct message* _) {
  return 0;
}

[[rc::parameters("fds_refn : fd_sched","p : loc")]]
[[rc::args("p @ &own<struct<struct_fd_scheduler,"
	   "uninit<{mk_array_layout i32 16}>,"
	   "uninit<u64>,"
	   "uninit<struct_npfp_scheduler>>>")]]
[[rc::ensures("own p: {"
	      "{|input_channels :=[];"
	      "sched_state := initialize_scheduler|}} @ fd_t")]]
[[rc::tactics("by apply list_subequiv_split; solve_goal.")]]
[[rc::tactics("have Hprio: priority = (Z.to_nat num_priorities); solve_goal.")]]
[[rc::tactics("by apply list_subequiv_split; solve_goal.")]]
[[rc::tactics("have Hi: i = (Z.to_nat num_msg_types); solve_goal.")]]
void fds_init(struct fd_scheduler* fds) {
  fds->num_channels = 0;
  // TODO: RefinedC currently does not accept the following:
  /* fds->sched.prio_levels = (prio_bitmap_t) { 0 }; */
  prio_level_init(&fds->sched.prio_levels);

  [[rc::exists("i : nat")]]
    [[rc::inv_vars("typ : i @ int<i32>")]]
    [[rc::inv_vars("fds : p @ &own<struct<struct_fd_scheduler,"
		   "uninit<{mk_array_layout i32 16}>,"
		   "{0} @ int<u64>,"
		   "struct<struct_npfp_scheduler,"
		   "array_p<{layout_of struct_callback}, {replicate i 0%nat `at_type` callback_t}, {((Z.to_nat num_msg_types) - i)%nat}>,"
		   "uninit<{mk_array_layout struct_message_queue (Z.to_nat num_priorities)}>,"
		   "{replicate (Z.to_nat num_priorities) false} @ prio_bitmap_t>>>")]]
    [[rc::constraints("{i <= num_msg_types}")]]
  for(int typ = 0; typ < NUM_MESSAGE_TYPES; typ += 1) {
    fds->sched.callbacks[typ] = (struct callback) {0, nop_callback};
  }

  [[rc::exists("priority : nat")]]
    [[rc::inv_vars("prio : priority @ int<i32>")]]
    [[rc::inv_vars("fds : p @ &own<struct<struct_fd_scheduler,"
           "uninit<{mk_array_layout i32 16}>,"
           "{0} @ int<u64>,"
           "struct<struct_npfp_scheduler,"
            "array<{layout_of struct_callback}, {replicate (Z.to_nat num_msg_types) 0%nat `at_type` callback_t}>,"
            "array_p<struct_message_queue, {replicate priority (@nil message_data) `at_type`  message_queue}, {((Z.to_nat num_priorities) - priority)%nat}>,"
            "{replicate (Z.to_nat num_priorities) false} @ prio_bitmap_t >>>")]]
    [[rc::constraints("{priority <= num_priorities}")]]
  for(int prio = 0; prio < NUM_PRIORITIES; prio += 1) {
    fds->sched.pending[prio] = (struct message_queue) {NULL, NULL};
    fds->sched.pending[prio].last = &fds->sched.pending[prio].first;
  }
}

[[rc::parameters("fd_state : fd_sched", "p : loc","fd : Z")]]
[[rc::args("p @ &own<fd_state @ fd_t>", "fd @ int<i32>")]]
[[rc::returns("{0} @ int<i32>")]]
[[rc::ensures("own p : {(fds_add_channel_func fd_state fd)} @ fd_t")]]
[[rc::requires("{length fd_state.(input_channels) < 16}")]]
[[rc::tactics("apply list_subequiv_split; solve_goal.")]]
int fds_add_channel(struct fd_scheduler* fds, int fd) {
  assert(fds->num_channels < MAX_INPUT_CHANNELS);

  /* mark as nonblocking */
  int err = fcntl(fd, F_SETFL, O_NONBLOCK);
  if (err)
    return err;

  fds->input_channels[fds->num_channels] = fd;
  fds->num_channels++;

  return 0;
}

[[rc::parameters("fds : fd_sched", "msg_type : nat", "prio : nat", "p : loc")]]
[[rc::args("p @ &own<fds @ fd_t>", "msg_type @ int<u8>","function_ptr<{"
	   "fn(∀ (msg, q) : message_data * loc;"
	   "(&own (msg @ (message (uninit (void*)))));True)→"
	   "∃ () : (), (int (i32));"
	   "True"
	   "}>", "prio @ int<u8>")]]
[[rc::ensures("own p : {(fds_set_callback_func fds msg_type prio)} @ fd_t")]]
[[rc::requires("{msg_type < num_msg_types}")]]
[[rc::requires("{prio < num_priorities}")]]
void fds_set_callback(struct fd_scheduler* fds,
           message_type_t type, callback_fn_t f, priority_t prio) {
  fds->sched.callbacks[type] = (struct callback) {prio, f};
}


static
int receive_one_message(struct fd_scheduler* fds, int fd) {
  /* NB: we really should use pre-allocated memory here to avoid page faults */
  struct message *msg = malloc(sizeof(*msg));

  /* we are not going to handle memory allocation failures */
  assert(msg);

  /* receive data from FD */
  int n = read(fd, &msg->data, MAX_MESSAGE_LEN);

  if (n <= 0) {
    // FIXME: should handle closed FDs gracefully
    free(msg);
    return n;
  } else {
    msg->len = n;
    npfp_enqueue(&fds->sched, msg);
    return 0;
  }
}

static
int receive_messages(struct fd_scheduler* fds, int fd) {
  int err;
  do {
    err = receive_one_message(fds, fd);
  } while (!err);

  if (errno == EWOULDBLOCK || errno == EAGAIN)
    /* nothing else to receive for now, this is fine */
    return 0;
  else
    return err;
}

static
int check_channels(struct fd_scheduler* fds) {
  int err;
  for (nfds_t ch = 0; ch < fds->num_channels; ch++) {
      err = receive_messages(fds, fds->input_channels[ch]);
      if (!err)
        return err;
  }
  return 0;
}

int fds_run(struct fd_scheduler* fds) {
  int err;

  assert(fds->num_channels > 0);

  while (1) {
    do {
      /* receive messages on all channels */
      err = check_channels(fds);
      if (err)
        return err;

      /* get the highest-priority message */
      struct message *msg = npfp_dequeue(&fds->sched);

      /* if there is no message, wait for new input */
      if (!msg)
        break;

      /* consume the message */
      err = npfp_dispatch(&fds->sched, msg);

      /* release the memory */
      free(msg);

      /* terminate if the callback failed for some reason */
      if (err)
        return err;
    } while (!err);
  }
}
