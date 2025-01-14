#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

/**
   Please look at proofs/lithium/lithium_tutorial.v for the tutorial.
 */

[[rc::parameters("n : Z")]]
[[rc::args("{n <> 0} @ optional<&own<n @ int<i32>>, null>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::manual_proof("refinedc.tutorial.lithium:lithium_tutorial, type_lithium_test")]]
int lithium_test(int *a) {
  if (a != NULL) {
    return *a + 0;
  } else {
    return 0;
  }
}
