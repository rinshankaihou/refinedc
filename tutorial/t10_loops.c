#include <refinedc.h>

// type checking of this function should terminate
[[rc::args("int<i32>")]]
[[rc::ensures("{True}")]]
void loop_without_annot(int a) {
  while(a == 1) {}

  [[rc::block]]
  while(a == 1) {}

  [[rc::full_block]]
  while(a == 1) {}
}
