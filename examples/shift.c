[[rc::parameters("x : nat")]]
[[rc::args("x @ int<u32>")]]
[[rc::requires("{2 * x ≤ max_int u32}")]]
[[rc::returns("{2 * x} @ int<u32>")]]
unsigned int times_two(unsigned int x){
  return x << 1;
}

[[rc::parameters("x : nat")]]
[[rc::args("x @ int<u32>")]]
[[rc::returns("{x `div` 2} @ int<u32>")]]
[[rc::tactics("by apply Z.shiftr_nonneg.")]]
[[rc::tactics("rewrite Z.shiftr_div_pow2 //; lia.")]]
[[rc::tactics("rewrite Z.shiftr_div_pow2 //.")]]
unsigned int div_two(unsigned int x){
  return x >> 1;
}
