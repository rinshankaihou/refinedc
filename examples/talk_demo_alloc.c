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
//@(*Definition byte_layout : nat → layout := ly_set_size u8.*)
//@Definition byte_layout : nat → layout := mk_array_layout u8.
//@Coercion byte_layout : nat >-> layout.
//@
//@Notation Uninit := (∃ₜ n : nat, uninit n)%I.
//@rc::end












struct [[rc::refined_by("a: nat")]] mem_t {
  [[rc::field("a @ int<size_t>")]] size_t len;
  [[rc::field("&own<uninit<a>>")]] unsigned char* buffer;
};

[[rc::parameters("p : loc", "a : nat", "n : nat")]]
[[rc::args   ("p @ &own<a @ mem_t>", "n @ int<size_t>")]]
[[rc::requires("{n <= a}")]]
[[rc::returns("&own<uninit<n>>")]]
[[rc::ensures("own p : {a - n} @ mem_t")]]
void* alloc(struct mem_t* d, size_t sz) {
  assert(sz <= d->len);
  d->len -= sz;
  return d->buffer + d->len;
}


[[rc::args("&own<{10} @ mem_t>")]]
[[rc::returns("{2} @ int<u8>")]]
char client(struct mem_t* d) {
  char *a = alloc(d, 3);
  a[0] = 0; a[1] = 1; a[2] = 2;
  char *x = a + 2;
  return *x;
}















/*
  Old instructions:
(emacs copy to register: C-x r s 1/2, insert from register: C-x r i 1/2)

change spec of alloc:
[[rc::args   ("&own<mem_t>", "int<size_t>")]]
[[rc::returns("optional<&own<Uninit>, null>")]]

->

change spec of client:
[[rc::args("&own<mem_t>")]]

->

change spec of alloc:
[[rc::parameters("n : nat")]]
[[rc::args   ("&own<mem_t>", "n @ int<size_t>")]]
[[rc::returns("optional<&own<uninit<n>>, null>")]]

->
add to body of client:
  struct xy * t = alloc(d, sizeof(struct xy));
  if(t == NULL) { return; }
  t->x = 0;

->

change spec of alloc:
[[rc::parameters("p : loc", "n : nat")]]
[[rc::args   ("p @ &own<mem_t>", "n @ int<size_t>")]]
[[rc::returns("optional<&own<uninit<n>>, null>")]]
[[rc::ensures("own p : mem_t")]]

->
change body of alloc:
  void *r = d->buffer;
  d->buffer += sz;
  return r;

*/
