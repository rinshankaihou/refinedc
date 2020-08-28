#include <stdint.h>

//@rc::inlined
//@Definition flags_type := (bool * bool * bool)%type.
//@
//@Definition flags_from_nat n :=
//@  let b0 := bool_decide (n `mod` 2 = 1) in
//@  let n  := n `div` 2 in
//@  let b1 := bool_decide (n `mod` 2 = 1) in
//@  let n  := n `div` 2 in
//@  let b2 := bool_decide (n `mod` 2 = 1) in
//@  let n  := n `div` 2 in
//@  if bool_decide (n = 0) then Some (b0, b1, b2) else None.
//@rc::end

typedef struct
[[rc::refined_by("f : flags_type")]]
[[rc::exists("n : nat")]]
[[rc::constraints("{flags_from_nat n = Some f}")]]
flags {
  [[rc::field("n @ int<u8>")]]
  uint8_t flags;
} flags_t;

#define IS_SET(f, n) (((f).flags >> (n)) % 2 == 1)

[[rc::parameters("f1 : bool", "f2 : bool", "f3 : bool")]]
[[rc::parameters("n1 : nat", "n2 : nat", "n3 : nat")]]
[[rc::args("{(f1, f2, f3)} @ flags")]]
[[rc::args("n1 @ int<u32>", "n2 @ int<u32>", "n3 @ int<u32>")]]
[[rc::requires("{n1 + n2 < it_max u32}")]]
[[rc::requires("{n2 + n3 < it_max u32}")]]
[[rc::requires("{n1 + n3 < it_max u32}")]]
[[rc::requires("{n1 + n2 + n3 < it_max u32}")]]
[[rc::returns("{(if f1 then n1 else 0) + (if f2 then n2 else 0) + (if f3 then n3 else 0)} @ int<u32>")]]
[[rc::trust_me]] // FIXME automation
unsigned int sum(flags_t f, unsigned int arg1, unsigned int arg2, unsigned int arg3){
  unsigned int r = 0;
  if(IS_SET(f, 0)) r += arg1;
  if(IS_SET(f, 1)) r += arg2;
  if(IS_SET(f, 2)) r += arg3;
  return r;
}
