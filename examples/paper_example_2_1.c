// Example of Section 2.1.

#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>
#include <spinlock.h>

//@rc::inlined
//@Notation "P ? l : r" :=
//@  (if bool_decide P then l else r)
//@  (at level 100, l at next level, r at next level).
//@
//@Close Scope Z.
//@
//@Definition byte_layout : nat → layout := ly_set_size u8.
//@Coercion byte_layout : nat >-> layout.
//@rc::end

struct [[rc::refined_by("a : nat")]] mem_t {
  [[rc::field("a @ int<size_t>")]] size_t len;
  [[rc::field("&own<uninit<a>>")]] unsigned char *buffer;
};

[[rc::parameters("a : nat", "n : nat", "p : loc")]]
[[rc::args   ("p @ &own<a @ mem_t>", "n @ int<size_t>")]]
[[rc::returns("{n ≤ a} @ optional<&own<uninit<n>>, null>")]]
[[rc::ensures("p @ &own<{n ≤ a ? a - n : a} @ mem_t>")]]
void *alloc(struct mem_t *d, size_t size) {
  if(size > d->len) return NULL;
  d->len -= size;
  return d->buffer + d->len;
}

// Thread-safe version (given in appendix).

[[rc::parameters("lid : lock_id")]]
[[rc::global("spinlock<lid>")]]
struct spinlock lock;

[[rc::parameters("lid : lock_id")]]
[[rc::global("spinlocked<lid, {\"data\"}, mem_t>")]]
struct mem_t data;

[[rc::parameters("lid : lock_id", "n : nat")]]
[[rc::args      ("n @ int<size_t>")]]
[[rc::requires  ("[initialized \"lock\" lid]", "[initialized \"data\" lid]")]]
[[rc::returns   ("optional<&own<uninit<n>>, null>")]]
void *thread_safe_alloc(size_t size) {
  sl_lock(&lock);
  rc_unlock(data);
  void *ret = alloc(&data, size);
  sl_unlock(&lock);
  return ret;
}

// Testing thread-safety.

// RefinedC does not have forking built-in at the moment.
// We axiomatize it using the following [fork] function.

typedef void (*fork_fun)(void *);

[[rc::parameters("ty : type", "P : {iProp Σ}")]]
[[rc::args("function_ptr<{fn(∀ () : (); &own ty; P) → ∃ () : (), void; True}>", "&own<ty>")]]
[[rc::requires("[P]")]]
void fork(fork_fun fn, void *arg){
  fn(arg); // Dummy implementation.
}

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
