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

// first show original code without annotations

struct [[rc::refined_by("a: nat")]] mem_t {
  [[rc::field("a @ int<size_t>")]] size_t len;
  [[rc::field("&own<uninit<a>>")]] unsigned char* buffer;
};

[[rc::args   ("&own<mem_t>", "int<size_t>")]]
[[rc::returns("optional<&own<Uninit>, null>")]]
void* alloc_1(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

[[rc::parameters("n: nat")]]
[[rc::args   ("&own<mem_t>", "n @ int<size_t>")]]
[[rc::returns("optional<&own<uninit<n>>, null>")]]
void* alloc_2(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

struct xy { char x, y; };

[[rc::args   ("&own<mem_t>")]]
void client_2(struct mem_t* d) {
  struct xy * s = alloc_2(d, sizeof(struct xy));
  if(s == NULL) { return; }
  s->x = 0;
}


[[rc::parameters("p : loc")]]
[[rc::args   ("p @ &own<mem_t>", "int<size_t>")]]
[[rc::returns("optional<&own<Uninit>, null>")]]
[[rc::ensures("own p : mem_t")]]
void* alloc_2_alt(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

[[rc::parameters("p : loc", "n: nat")]]
[[rc::args   ("p @ &own<mem_t>", "n @ int<size_t>")]]
[[rc::returns("optional<&own<uninit<n>>, null>")]]
[[rc::ensures("own p : mem_t")]]
void* alloc_3(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

[[rc::parameters("a: nat", "n: nat", "p: loc")]]
[[rc::args   ("p @ &own<a @ mem_t>", "n @ int<size_t>")]]
[[rc::returns("{n ≤ a} @ optional<&own<uninit<n>>, null>")]]
[[rc::ensures("own p : {n ≤ a ? a - n : a} @ mem_t")]]
void* alloc_full(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  return d->buffer + d->len;
}

[[rc::args   ("&own<mem_t>")]]
void client_full(struct mem_t* d) {
  struct xy * s = alloc_full(d, sizeof(struct xy));
  if(s == NULL) { return; }
  s->x = 0;
  struct xy * t = alloc_full(d, sizeof(struct xy));
  if(t == NULL) { return; }
  t->x = 0;
}

[[rc::parameters("a: nat", "n: nat", "p: loc")]]
[[rc::args   ("p @ &own<a @ mem_t>", "n @ int<size_t>")]]
[[rc::returns("{n ≤ a} @ optional<&own<uninit<n>>, null>")]]
[[rc::ensures("own p : {n ≤ a ? a - n : a} @ mem_t")]]
void* alloc_from_start(struct mem_t* d, size_t sz) {
  if(sz > d->len) return NULL;
  d->len -= sz;
  unsigned char *res = d->buffer;
  d->buffer += sz;
  return res;
}
