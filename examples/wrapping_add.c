#include <stddef.h>
#include <refinedc.h>

#define WRAPPING_ADD(it1, it2, a, b) RC_MACRO(WrappingAdd, (a) + (b), \
     RC_MACRO_ARG(it1), RC_MACRO_ARG(it2), RC_MACRO_EXPR(a), RC_MACRO_EXPR(b))

//@rc::import wrapping_def from refinedc.examples.wrapping_add (for code only)
//@rc::import wrapping_rules from refinedc.examples.wrapping_add

[[rc::parameters("a : Z", "b : Z", "c : Z")]]
[[rc::args("a @ int<size_t>", "b @ int<size_t>", "c @ int<size_t>")]]
[[rc::requires("{(b + c < int_modulus size_t)}")]]
/* We don't want to add the following: [[rc::requires("{(a + b < int_modulus size_t)}")]] */
[[rc::returns("{((a + (b + c)) `mod` int_modulus size_t)} @ int<size_t>")]]
size_t wrapping_add(size_t a, size_t b, size_t c) {
  return WRAPPING_ADD(size_t, size_t, a, (b + c));
}
