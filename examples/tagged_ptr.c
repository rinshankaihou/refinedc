#include <stddef.h>
#include <stdint.h>
#include <refinedc.h>

//@rc::import tagged_ptr_extra from refinedc.examples.tagged_ptr (for proofs only)

#define TAG_SIZE 3ULL
#define TAG_MOD  (1ULL << TAG_SIZE)
#define TAG_MASK (TAG_MOD - 1)

//@rc::inlined Notation TAG_MOD := (8%nat) (only parsing).

[[rc::parameters("r: {loc * Z}", "ty: type", "v: val")]]
[[rc::args("at_value<v, r @ &tagged<TAG_MOD, ty>>")]]
[[rc::requires("[type_alive_own ty]")]]
[[rc::returns("{r.2} @ int<u8>")]]
[[rc::ensures("v : r @ &tagged<TAG_MOD, ty>", "{0 ≤ r.2 < TAG_MOD}")]]
[[rc::tactics("all: rewrite Z_land_add_l; solve_goal.")]]
unsigned char tag_of(void* p){
  uintptr_t i = (uintptr_t) p;
  unsigned char t = i & TAG_MASK;
  return t;
}

[[rc::parameters("r: {loc * Z}", "t: Z", "ty: type")]]
[[rc::args("r @ &tagged<TAG_MOD, ty>", "t @ int<u8>")]]
[[rc::requires("{0 ≤ t < TAG_MOD}", "[type_alive_own ty]")]]
[[rc::returns("{(r.1, t)} @ &tagged<TAG_MOD, ty>")]]
[[rc::tactics("all: rewrite Z_lor_land_not; solve_goal.")]]
void* tag(void* p, unsigned char t){
  uintptr_t i = (uintptr_t) p;
  uintptr_t new_i = (i & ~ TAG_MASK) | t;
  void* q = copy_alloc_id(new_i, p);
  return q;
}

[[rc::parameters("r: {loc * Z}", "ty: type")]]
[[rc::args("r @ &tagged<TAG_MOD, ty>")]]
[[rc::requires("[type_alive_own ty]")]]
[[rc::returns("{r.1} @ &own<ty>")]]
void* untag(void* p){
  return tag(p, 0);
}

[[rc::parameters("r: {loc * Z}", "ty: type")]]
[[rc::args("r @ &tagged<TAG_MOD, ty>")]]
[[rc::requires("[type_alive_own ty]")]]
[[rc::returns("{r.1} @ &own<ty>")]]
void* untag2(void* p){
  uintptr_t i = (uintptr_t) p;
  return copy_alloc_id(i - i % TAG_MOD, p);
}

[[rc::returns("{0} @ int<size_t>")]]
size_t test(){
  size_t x = 0;

  void *tp = tag(&x, 1);
  assert(tag_of(tp) == 1);

  size_t *px = (size_t *) untag(tp);
  return *px;
}

[[rc::parameters("l: loc", "n: Z")]]
[[rc::args("l @ &own<n @ int<i32>>")]]
[[rc::returns("{bool_decide (l `aligned_to` 8%nat)} @ boolean<i32>")]]
[[rc::ensures("own l : n @ int<i32>")]]
[[rc::tactics("all: unfold_aligned_to; split; solve_goal.")]]
int is_aligned(void* p){
  uintptr_t i = (uintptr_t) p;
  return i % TAG_MOD == 0;
}
