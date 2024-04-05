#include <assert.h>
#include <errno.h>
#include <stddef.h>


#include "sys/system.h"
#include "fdsched.h"

#include "fcntl_specs.h"
#include "../include/read_specs.h"
#include "../../include/refinedc_malloc.h"

//@rc::import fdsched_extra from refinedc.examples.scheduler.src.fdsched

[[rc::parameters("msg : message_data", "q : loc")]]
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

  // TODO: improve performance of RefinedC using an opaque version of replicate / making (Z.to_nat num_priorities) opaque?
  [[rc::exists("i : nat")]]
    [[rc::inv_vars("typ : i @ int<i32>")]]
    [[rc::inv_vars("fds : p @ &own<struct<struct_fd_scheduler,"
		   "uninit<{mk_array_layout i32 16}>,"
		   "{0} @ int<u64>,"
		   "struct<struct_npfp_scheduler,"
		   "array_p<{layout_of struct_callback}, {replicate i 0%nat `at_type` callback_t}, {Z.to_nat num_msg_types}>,"
		   "uninit<{mk_array_layout struct_message_queue (Z.to_nat num_priorities)}>,"
		   "{replicate (Z.to_nat num_priorities) false} @ prio_bitmap_t>>>")]]
    [[rc::constraints("{i ≤ num_msg_types}")]]
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
            "array_p<struct_message_queue, {replicate priority (@nil message_data) `at_type`  message_queue}, {Z.to_nat num_priorities}>,"
            "{replicate (Z.to_nat num_priorities) false} @ prio_bitmap_t >>>")]]
    [[rc::constraints("{priority ≤ num_priorities}")]]
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

[[rc::parameters("fd_state : fd_sched", "p1 : loc","fd : Z","t1 : nat", "errno : Z")]]
[[rc::args("p1 @ &own<fd_state @ fd_t>", "fd @ int<i32>")]]
[[rc::requires("[curr_read_index t1]")]]
[[rc::requires("[is_errno errno]")]]
[[rc::exists( "n : Z")]]
[[rc::returns("{if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then 0 else -1} @ int<i32>")]]
[[rc::ensures("[curr_read_index (t1 + 1)%nat]")]]
[[rc::ensures("own p1 : {receive_one_message_func t1 fd fd_state} @ fd_t")]]
[[rc::ensures("[is_errno n]")]]
[[rc::ensures("{if (bool_decide $ is_Some $ (packet_arrivals fd t1)) then True else n = 80}")]]
[[rc::tactics("all: destruct (packet_arrivals fd t1) eqn:E; try solve_goal.")]]
[[rc::tactics("by apply packet_data_len.")]]
[[rc::tactics("rewrite get_packet_data_no_pending => //=; eexists; solve_goal.")]]
[[rc::tactics("by rewrite get_packet_data_no_pending.")]]
[[rc::tactics("by rewrite receive_one_message_no_pending.")]]
[[rc::tactics("by rewrite /add_pending_msg_to_scheduler E.")]]
static
int receive_one_message(struct fd_scheduler* fds, int fd) {
  /* NB: we really should use pre-allocated memory here to avoid page faults */
  struct message *msg = xmalloc(sizeof(*msg));

  /* we are not going to handle memory allocation failures */
  assert(msg);

  /* receive data from FD */
  int n = read(fd, &msg->data, MAX_MESSAGE_LEN);

  if (n < 0) {
    // FIXME: should handle closed FDs gracefully
    free(msg);
    return n;
  } else {
    msg->len = n;
    npfp_enqueue(&fds->sched, msg);
    return 0;
  }
}

// When the return value is non-negative it is a flag for whether we actually received a message otherwise it's an error flag (-1)
[[rc::parameters("fd_state : fd_sched", "p1 : loc","fd : Z","t1 : nat", "errno : Z")]]
[[rc::args("p1 @ &own<fd_state @ fd_t>", "fd @ int<i32>")]]
[[rc::requires("[curr_read_index t1]")]]
[[rc::requires("[is_errno errno]")]]
[[rc::exists("m : nat", "flag : Z", "errno : Z")]]
[[rc::returns("flag @ int<i32>")]]
[[rc::ensures("[curr_read_index (t1 + (S m))]")]]
[[rc::ensures("[is_errno errno]")]]
[[rc::ensures("{fd_has_n_msgs fd m t1}")]]
[[rc::ensures("{flag = bool_to_Z (bool_decide (m <> 0))%nat}")]]
[[rc::ensures("own p1 : {receive_n_messages_func t1 fd fd_state (S m)} @ fd_t")]]
[[rc::tactics("all: rewrite <- ?Nat.add_assoc, ?Nat.add_1_r; try apply simpl_fd_has_msgs_S; solve_goal.")]]
static
int receive_messages(struct fd_scheduler* fds, int fd) {
  int err;
  int non_empty = 0;


  [[rc::exists("i : nat", "err : Z", "flag : Z")]]
  [[rc::exists("fd_state_mid : fd_sched", "n : Z")]]
  [[rc::inv_vars("err : err @ int<i32>")]]
  [[rc::inv_vars("fds : p1 @ &own<fd_state_mid @ fd_t>")]]
  [[rc::inv_vars("non_empty : flag @ int<i32>")]]
  [[rc::constraints("[curr_read_index (t1 +  (S i))]")]]
  [[rc::constraints("{if (bool_decide $ is_Some $ (packet_arrivals fd (t1 +  i))) then err = 0"
		    " else err = -1}")]]
  [[rc::constraints("{ flag = if (decide (i = 0)%nat) then bool_to_Z (err =? 0) else 1}")]]
  [[rc::constraints("{fd_state_mid = receive_n_messages_func t1 fd fd_state (S i)}")]]
  [[rc::constraints("[is_errno n]")]]
  [[rc::constraints("{if (bool_decide $ is_Some $ (packet_arrivals fd (t1 +   i))) then True else n = 80}")]]
  [[rc::constraints("{fd_has_at_least_n_msgs fd i t1}")]]
  do {
    err = receive_one_message(fds, fd);
    if (!err) non_empty = 1;
  }
  while (!err);

  if (errno == EWOULDBLOCK || errno == EAGAIN)
    /* nothing else to receive for now, this is fine */
    return non_empty;
  else
    return err;
}


// When the return value is non-negative it is a flag for whether we actually received a message otherwise it's an error flag (-1)
//all messages received on all channels till time t have been read and added to the scheduler
//calls recv messages on fd i for ni times
[[rc::parameters("fd_state : fd_sched", "p1 : loc", "t1 : nat", "errno : Z")]]
[[rc::args("p1 @ &own<fd_state @ fd_t>")]]
[[rc::requires("[curr_read_index t1]")]]
[[rc::requires("[is_errno errno]")]]
[[rc::exists("ns : {list nat}", "flag : Z", "errno : Z")]]
[[rc::returns("flag @ int<i32>")]]
[[rc::ensures("[curr_read_index (t1 + num_reads_for_ns ns)%nat]")]]
[[rc::ensures("[is_errno errno]")]]
[[rc::ensures("{flag = bool_to_Z (bool_decide (Exists (λ n, (n <> 0)%nat) ns))}")]]
[[rc::ensures("own p1 : {check_n_channels_func t1 fd_state (length (input_channels fd_state)) ns} @ fd_t")]]
[[rc::ensures("{fds_have_n_msgs (input_channels fd_state) ns t1}")]]
[[rc::tactics("all: simplify_channels; try solve_goal.")]]
[[rc::tactics("rewrite Nat.add_1_r; erewrite take_S_r => //; apply fds_have_n_msgs_next_fd => //.")]]
[[rc::tactics("apply Exists_app; right; apply Exists_cons_hd; solve_goal.")]]
[[rc::tactics("rewrite receive_one_message_no_pending; by [ apply fd_has_n_msgs_implies_no_pending | rewrite -check_n_channels_S ].")]]
[[rc::tactics("rewrite Nat.add_1_r; erewrite take_S_r => //; apply fds_have_n_msgs_next_fd => //.")]]
[[rc::tactics("assert (¬ ((λ n, n <> 0) x')%nat) as HP by solve_goal; eapply Exists_last_false in HP; solve_goal.")]]
[[rc::tactics("rewrite receive_one_message_no_pending; by [ apply fd_has_n_msgs_implies_no_pending | rewrite -check_n_channels_S ].")]]
[[rc::tactics("repeat f_equal; lia.")]]
[[rc::tactics("erewrite <- (take_ge (input_channels _)) => //; lia.")]]
static int check_channels(struct fd_scheduler* fds) {
  int fd, err, flag = 0;

  [[rc::exists("i : nat", "errno : Z")]]
  [[rc::exists("fd_state_mid : fd_sched")]]
  [[rc::exists("ns : {list nat}", "flag : Z")]]
  [[rc::inv_vars("ch : i @ int<u64>")]]
  [[rc::inv_vars("fds : p1 @ &own<fd_state_mid @ fd_t>")]]
  [[rc::inv_vars("flag : flag @ int<i32>")]]
  [[rc::constraints("[curr_read_index (t1 + (num_reads_for_ns ns))]")]]
  [[rc::constraints("[is_errno errno]")]]
  [[rc::constraints("{fds_have_n_msgs (take i (input_channels fd_state)) ns t1}")]]
  [[rc::constraints("{ flag = bool_to_Z (bool_decide (Exists (λ n, (n <> 0)%nat) ns))}")]]
  [[rc::constraints("{fd_state_mid = check_n_channels_func t1 fd_state i ns}")]]
  [[rc::constraints("{(0 ≤ i ≤ length (input_channels fd_state))%nat}")]]
  for (nfds_t ch = 0; ch < fds->num_channels; ch++) {
    fd = fds->input_channels[ch];
    err = receive_messages(fds, fd);
    if (err < 0)
      return err;
    if (err > 0)
      flag = 1;
  }
  return flag;
}

[[rc::parameters("fd_state : fd_sched", "p1 : loc", "t1 : nat", "errno : Z")]]
[[rc::args("p1 @ &own<fd_state @ fd_t>")]]
[[rc::requires("[curr_read_index t1]")]]
[[rc::requires("[is_errno errno]")]]
[[rc::exists("ns_list : {list (list nat)}")]]
[[rc::returns("{0} @ int<i32>")]]
[[rc::ensures("[curr_read_index (t1 + num_reads_for_ns_list ns_list)]")]]
[[rc::ensures("own p1 : {check_channels_until_empty_func t1 fd_state ns_list} @ fd_t")]]
[[rc::ensures("{fds_have_ns_list_msgs_done (input_channels fd_state) ns_list t1}")]]
[[rc::tactics("all: simplify_channels; clear_cases; try solve_goal.")]]
[[rc::tactics("2,3: destruct (bool_decide_reflect (err = 0)); first lia.")]]
[[rc::tactics("case_bool_decide => //=; by apply fds_have_ns_list_msgs_done_base_run.")]]
[[rc::tactics("case_bool_decide; by [ apply fds_have_ns_list_msgs_next_loop | apply fds_have_ns_list_msgs_done_next_run].")]]
[[rc::tactics("by rewrite check_channels_until_empty_next.")]]
int check_channels_until_empty(struct fd_scheduler* fds){
  int err;

  [[rc::exists("err : Z", "errno : Z")]]
  [[rc::exists("fd_state_mid : fd_sched")]]
  [[rc::exists("ns_list : {list (list nat)}", "flag : Z")]]
  [[rc::inv_vars("err : err @ int<i32>")]]
  [[rc::inv_vars("fds : p1 @ &own<fd_state_mid @ fd_t>")]]
  [[rc::constraints("{0 <= err}")]]
  [[rc::constraints("[curr_read_index (t1 + (num_reads_for_ns_list ns_list))]")]]
  [[rc::constraints("[is_errno errno]")]]
  [[rc::constraints("{if (bool_decide (err = 0)) then \
											fds_have_ns_list_msgs_done (input_channels fd_state) ns_list t1 else \
 											fds_have_ns_list_msgs (input_channels fd_state) ns_list t1}")]]
  [[rc::constraints("{fd_state_mid = check_channels_until_empty_func t1 fd_state ns_list}")]]
  do {
    err = check_channels(fds);
    if (err < 0)
      return err;
  } while (err > 0);

  return err;
}

// fds after one iteration will just be (npfp_dequeue (check_channels fds))
int fds_run(struct fd_scheduler *fds) {
  int err;

  assert(fds->num_channels > 0);

  while (1) {
    do {
      /* receive messages on all channels */
      err = check_channels_until_empty(fds);

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
