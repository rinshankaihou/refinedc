#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

/* Let's start with a simple function that computes the average of two
 * on unsigned integers. This function might seem correct but it
 * actually has a bug. Do you see it? */
unsigned int avg_1(unsigned int a, unsigned int b) {
  return (a + b) / 2;
}


/* Let's try to verify this function using RefinedC to see if it finds
 * a problem.

   Explain rc::args and rc::returns...
 */
[[rc::args("int<u32>", "int<u32>")]]
[[rc::returns("int<u32>")]]
[[rc::trust_me]]
unsigned int avg_2(unsigned int a, unsigned int b) {
  return (a + b) / 2;
}

/* RefinedC shows an error. TODO: Explain that error shows that there
 * is a possible overflow. RefinedC by default proves that there is no
 * overflow.

   Bug: avg is incorrect if there is overflow!
   E.g. avg(0x80000000U, 0x80000000U) = 0, not 0x80000000U!
 */


/* Multiple ways to fix this. One is to detect which integer is lower
 * and then adding half the difference:
*/
[[rc::args("int<u32>", "int<u32>")]]
[[rc::returns("int<u32>")]]
unsigned int avg_3(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}

/* RefinedC proves that there are no overflows in this algorithm! But
 * is it actually correct? */

/* RefinedC can verify functional correctness using refinement types.
 * Explain...
*/

[[rc::parameters("na : Z", "nb : Z")]]
[[rc::args("na @ int<u32>", "nb @ int<u32>")]]
[[rc::exists("r : Z")]]
[[rc::returns("r @ int<u32>")]]
[[rc::ensures("{na `min` nb <= r}")]]
[[rc::ensures("{r <= na `max` nb}")]]
[[rc::ensures("{r = (na + nb) `div` 2}")]]
unsigned int avg_4(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}

[[rc::parameters("na : Z", "nb : Z")]]
[[rc::args("na @ int<u32>", "nb @ int<u32>")]]
[[rc::returns("{(na + nb) `div` 2} @ int<u32>")]]
unsigned int avg_5(unsigned int a, unsigned int b) {
  unsigned int low = (a < b) ? a : b;
  unsigned int high = (a < b) ? b : a;
  return low + (high - low) / 2;
}
