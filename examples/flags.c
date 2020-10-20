#include <stdint.h>

//@rc::inlined
//@Record Flags := mkFlags {
//@  flag1 : bool ;
//@  flag2 : bool ;
//@}.
//@
//@Definition nat_encodes_flags n fs :=
//@  Z.testbit 0 n = flag1 fs ∧
//@  Z.testbit 1 n = flag2 fs ∧
//@  ∀ k, k > 1 → ¬ Z.testbit k n.
//@rc::end

typedef struct
[[rc::refined_by("f : Flags")]]
[[rc::exists("n : nat")]]
[[rc::constraints("{nat_encodes_flags n f}")]]
flags {
  [[rc::field("n @ int<u8>")]]
  uint8_t flags;
} flags_t;

#define IS_SET(f, n) (((f).flags >> (n)) & 1)

[[rc::parameters("fs : Flags", "n1 : nat", "n2 : nat")]]
[[rc::args("fs @ flags", "n1 @ int<u32>", "n2 @ int<u32>")]]
[[rc::requires("{n1 + n2 ≤ max_int u32}")]]
[[rc::returns("{(if flag1 fs then n1 else 0) + (if flag2 fs then n2 else 0)} @ int<u32>")]]
[[rc::trust_me]] // FIXME automation
unsigned int sum(flags_t f, unsigned int arg1, unsigned int arg2){
  unsigned int r = 0;
  if(IS_SET(f, 0)) r += arg1;
  if(IS_SET(f, 1)) r += arg2;
  return r;
}
