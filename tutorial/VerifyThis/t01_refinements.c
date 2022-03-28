#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

/* Let's start with a simple function that computes the average of two
   on unsigned integers. This function might seem correct but it
   actually has a bug. Do you see it? */
unsigned int avg_1(unsigned int a, unsigned int b) {
  return (a + b) / 2;
}


/* Let's try to verify this function using RefinedC to see if it finds
   a problem. */
// The arguments have the RefinedC integer type int<u32>. (The naming
// of u32 follows Rust, i.e. u32 -> unsigned 32-bit integer, i8 ->
// signed 8-bit integer...)
[[rc::args("int<u32>", "int<u32>")]]
[[rc::returns("int<u32>")]] // This function returns a integer.
[[rc::trust_me]] // comment out this line to enable typechecking
unsigned int avg_2(unsigned int a, unsigned int b) {
  return (a + b) / 2;
}

/* RefinedC shows an error. Can you guess what the error means? */

/* SOLUTION:

   The error tells us that RefinedC cannot prove that the addition
   does not overflow. By default RefinedC proves absence of all
   overflow and underflow (even for unsigned integers).

   Can you now say what the bug in avg is? Which inputs trigger the
   bug?
*/


/*
  SOLUTION:
  Bug: avg is incorrect if there is overflow!
  E.g. avg(0x80000000U, 0x80000000U) = 0, not 0x80000000U!
 */


/* There are multiple ways to fix this bug. One is to detect which
 * integer is lower and then adding half the difference. (For more
 * discussion of the subtleties of implemeting this function see
 * https://www.youtube.com/watch?v=sBtAGxBh-XI .)
*/
[[rc::args("int<u32>", "int<u32>")]]
[[rc::returns("int<u32>")]]
unsigned int avg_3(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}

/* RefinedC proves that there are no overflows in this algorithm! But
   is it actually correct?

   Let's verify the functional correctness of avg using refinement types!
*/

// rc::parameters introduces universally quantified parameters for
// this function (here using the Coq type Z for mathematical
// integers).
[[rc::parameters("na : Z", "nb : Z")]]
// We refine the first argument with na (resulting in the type na @
// int<u32>) to state that the first argument has value na. Same for
// the second argument and nb.
[[rc::args("na @ int<u32>", "nb @ int<u32>")]]
// rc::exists introduces existentially quantified values for the
// result and postcondition of the function.
[[rc::exists("r : Z")]]
// We use refinement types to say that avg returns the integer r.
[[rc::returns("r @ int<u32>")]]
// Now we can write postconditions using na, nb and r. For example,
// the result value r is greater or equal than the minimum of na and
// nb.
[[rc::ensures("{na `min` nb <= r}")]]
// Or r is less or equal to the maximum of na and nb.
[[rc::ensures("{r <= na `max` nb}")]]
// Or r is the average of na and nb. This is computed on mathematical
// integers so there are no overflow problems here.
[[rc::ensures("{r = (na + nb) `div` 2}")]]
unsigned int avg_4(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}

[[rc::parameters("na : Z", "nb : Z")]]
[[rc::args("na @ int<u32>", "nb @ int<u32>")]]
// If we know the concrete value for r, we can also directly use it as
// the refinement of the return type.
[[rc::returns("{(na + nb) `div` 2} @ int<u32>")]]
unsigned int avg_5(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}

/* Ok, integers are cool, but what about pointers? Continue at
 * t02_ownership.c to find out!
 */
