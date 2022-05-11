#pragma once

#include <assert.h>
#include <stdint.h>
#include <stddef.h>

/* message type, for the user-defined way of mapping input to callbacks */
typedef uint8_t message_type_t;
#define NUM_MESSAGE_TYPES (UINT8_MAX + 1)

//@rc::inlined
//@Record message_data := Message {
//@  m_type : Z;
//@  m_length : Z;
//@  m_data : list Z;
//@}.
//@Global Instance message_data_inhabited : Inhabited message_data := populate (Message inhabitant inhabitant inhabitant).
//@rc::end

/* a message that was received via some input channel */
struct [[rc::parameters("cont : type")]]
       [[rc::refined_by("data : message_data")]]
     message {
  [[rc::field("{m_type data} @ int<u8>")]]
  message_type_t type;
  [[rc::field("{m_length data} @ int<u64>")]]
  size_t len;

  /* embedded singly linked list of messages */
  [[rc::field("cont")]]
  struct message *next;

#define MAX_MESSAGE_LEN (4096 - sizeof(message_type_t) - sizeof(size_t) - sizeof(struct message*))
  [[rc::field("array<u8, {m_data data `at_type` int u8}>")]]
  uint8_t data[MAX_MESSAGE_LEN];
};

/* interface: we expect the user to provide an implementation of this
   function */
message_type_t message_identify_type(struct message* msg);


/* a simple FIFO queue of messages */
struct [[rc::refined_by("messages : {list message_data}")]]
       [[rc::ptr_type("message_queue : ∃ p. own_constrained<tyown_constraint<p, null>, ...>")]]
    message_queue {
  [[rc::field("tyfold<{(λ data cont, &own (data @ message cont) : type) <$> messages}, place<p>>")]]
  struct message *first;
  [[rc::field("&own<place<p>>")]]
  struct message **last;
};

/* enqueue at end */
[[rc::parameters("data : {list message_data}", "msg : message_data", "q : loc")]]
[[rc::args("q @ &own<data @ message_queue>",
           "&own<msg @ message<uninit<void*>>>")]]
[[rc::ensures("own q : {data ++ [msg]} @ message_queue")]]
static inline
void message_queue_add(struct message_queue *q, struct message *msg) {
  msg->next = NULL;
  *q->last = msg;
  q->last = &msg->next;
}


/* predicate: is the queue empty? */
[[rc::parameters("data : {list message_data}", "q : loc")]]
[[rc::args("q @ &own<data @ message_queue>")]]
[[rc::returns("{bool_decide (data = [])} @ boolean<i32>")]]
[[rc::ensures("own q : data @ message_queue")]]
static inline
int message_queue_empty(struct message_queue *q) {
  return q->first == NULL;
}

/* dequeue from front */
[[rc::parameters("data : {list message_data}", "msg : message_data", "q : loc")]]
[[rc::args("q @ &own<{msg::data} @ message_queue>")]]
[[rc::returns("&own<msg @ message<uninit<void*>>>")]]
[[rc::ensures("own q : data @ message_queue")]]
static inline
struct message* message_queue_remove(struct message_queue *q) {
  assert(!message_queue_empty(q));

  struct message* head = q->first;

  /* check if we're emptying the queue */
  if (head->next == NULL) {
    /* the queue is now empty */
    q->first = NULL;
    q->last = &q->first;
  } else {
    q->first = head->next;
  }
  return head;
}
