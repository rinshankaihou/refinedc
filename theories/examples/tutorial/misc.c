#include <stddef.h>
#include <stdbool.h>
#include "../inc/refinedc.h"
#include "../inc/spinlock.h"

struct [[rc::refined_by("nlen : nat")]] alloc_data {
  [[rc::field("nlen @ int<size_t>")]]
  size_t len;
  [[rc::field("&own<uninit<{ly_set_size u8 nlen}>>")]]
  unsigned char *buffer;
};
[[rc::parameters("nlen : nat", "nsize : nat", "p : loc")]]
[[rc::args("p @ &own<nlen @ alloc_data>", "nsize @ int<size_t>")]]
[[rc::returns("{nsize <= nlen} @ optional<&own<uninit<{ly_set_size u8 nsize}>>, null>")]]
[[rc::ensures("p @ &own<{if bool_decide(nsize <= nlen) then (nlen - nsize)%nat else nlen} @ alloc_data>")]]
void *alloc(struct alloc_data *d, size_t size) {
  if(size > d->len) {
    return NULL;
  }
  d->len -= size;
  return d->buffer + d->len;
}

[[rc::parameters("lid : lock_id")]]
[[rc::global("spinlock<lid>")]]
struct spinlock lock;

[[rc::parameters("lid : lock_id")]]
[[rc::global("spinlocked<lid, {\"data\"}, alloc_data>")]]
struct alloc_data data;

[[rc::parameters("lid : lock_id", "nsize : nat")]]
[[rc::args      ("nsize @ int<size_t>")]]
[[rc::requires  ("[initialized \"lock\" lid]", "[initialized \"data\" lid]")]]
[[rc::returns   ("optional<&own<uninit<{ly_set_size u8 nsize}>>, null>")]]
void *thread_safe_alloc(size_t size) {
  sl_lock(&lock);
  rc_unlock(data);
  void *ret = alloc(&data, size);
  sl_unlock(&lock);
  return ret;
}


typedef struct
[[rc::refined_by("s: {gmultiset layout}")]]
[[rc::ptr_type("chunks_t : {s ≠ ∅} @ optional<&own<...>, null>")]]
[[rc::exists("ly : layout", "tail : {gmultiset layout}")]]
[[rc::size("ly")]]
[[rc::constraints("{s = {[ly]} ⊎ tail}", "{∀ k, k ∈ tail → ly.(ly_size) ≤ k.(ly_size)}")]]
chunk {
  [[rc::field("{ly.(ly_size)} @ int<size_t>")]] size_t size;
  [[rc::field("tail @ chunks_t")]] struct chunk* next;
}* chunks_t;

[[rc::parameters("s : {gmultiset layout}", "p : loc", "ly : layout")]]
[[rc::args("p @ &own<s @ chunks_t>", "&own<uninit<ly>>", "{ly.(ly_size)} @ int<size_t>")]]
[[rc::requires("{layout_of struct_chunk ⊑ ly}")]]
[[rc::ensures("p @ &own<{{[ly]} ⊎ s} @ chunks_t>")]]
[[rc::tactics("all: multiset_solver.")]]
void free(chunks_t* list, void *data, size_t size) {
  chunks_t *cur = list;
  [[rc::exists("cp : loc", "cs : {gmultiset layout}")]]
  [[rc::inv_vars("cur : cp @ &own<cs @ chunks_t>")]]
  [[rc::inv_vars("list : p @ &own<wand<{cp ◁ₗ ({[ly]} ⊎ cs) @ chunks_t}, {{[ly]} ⊎ s} @ chunks_t>>")]]
  while(*cur != NULL) {
    if(size <= (*cur)->size) break;
    cur = &(*cur)->next;
  }
  chunks_t entry = data;
  entry->size = size;
  entry->next = *cur;
  *cur = entry;
}

/** Testing the thread-safety of thread_safe alloc */

// RefinedC does not have forking built-in at the moment, so we axiomatize it using the following [fork] function
typedef void (*fork_fun)(void *);
[[rc::parameters("ty : type", "P : {iProp Σ}")]]
[[rc::args("function_ptr<{fn(∀ () : (); &own ty; P) → ∃ () : (), void; True}>", "&own<ty>")]]
[[rc::requires("[P]")]]
void fork(fork_fun fn, void *arg);

[[rc::args("&own<∃ n : nat. n @ int<size_t>>")]]
[[rc::requires("[∃ lid : gname, initialized \"lock\" lid ∗ initialized \"data\" lid]")]]
void test_thread_safe_alloc_fork_fn(void *num) {
  size_t *num_int = num;
  thread_safe_alloc(*num_int);
}

size_t param;

[[rc::parameters("lid : gname")]]
[[rc::requires("[initialized \"lock\" lid]", "[initialized \"data\" lid]")]]
[[rc::requires("[global_with_type \"param\" Own (uninit size_t)]")]]
void test_thread_safe_alloc() {
  param = 5;
  fork(test_thread_safe_alloc_fork_fn, &param);
  thread_safe_alloc(5);
}
