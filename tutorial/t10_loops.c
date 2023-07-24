#include <refinedc.h>

// type checking of this function should terminate
[[rc::args("int<i32>", "int<i32>", "int<i32>")]]
[[rc::ensures("{True}")]]
void loop_without_annot(int a, int b, int c) {
  int z;
  while(a == 1) {}

  [[rc::block]]
  while(b == 1) {}

  [[rc::full_block]]
  while(c == 1) {}
}
