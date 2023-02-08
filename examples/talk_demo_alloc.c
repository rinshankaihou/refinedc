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
//@
//@Notation Uninit := (∃ₜ n : nat, uninit n)%I.
//@rc::end












struct [[rc::refined_by("a: nat")]] mem_t {
  [[rc::field("a @ int<size_t>")]] size_t len;
  [[rc::field("&own<uninit<a>>")]] unsigned char* buffer;
};

void* alloc(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

struct xy { char x, y; };

void client(struct mem_t* d) {
  struct xy * s = alloc(d, sizeof(struct xy));
  if(s == NULL) { return; }
  s->x = 0;
}















/*
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
