#include <stddef.h>
#include <stdbool.h>
// Random tests.

[[rc::returns("void")]]
void test1(){
  long long ll = 0;
  long l = 0;
  int i = 0;
  short s = 0;
  char c = 0;

  if(ll == l) return;
  if(ll == l) return;
  if(ll == i) return;
  if(ll == s) return;
  if(ll == c) return;

  if(!ll) return;
  if(!l) return;
  if(!i) return;
  if(!s) return;
  if(!c) return;

  return;
}

[[rc::returns("{1} @ int<i32>")]]
int return1(){
  return 1;
}

[[rc::requires("False")]]
int unreachable(){
  assert(1 == 2);
}

[[rc::returns("void")]]
void test_ternary(){
  int local = 0;
  assert((2 ? 3 : 2) == 3);
  assert((&local != NULL ? (return1() ? return1() : unreachable()) + 3 : 2) == 4);
}

[[rc::returns("void")]]
void test_bits() {
  // resource: https://en.cppreference.com/w/c/language/operator_arithmetic
  unsigned int mask = 0x00f0; // try uint16_t when issue #34 is fixed
  unsigned int a = 0x12345678;
  unsigned int setting_bits = a | mask;
  unsigned int selecting_bits = a & mask;
  unsigned int clearing_bits = a & ~mask;
  assert(setting_bits == 0x123456f8);
  assert(selecting_bits == 0x70);
  assert(clearing_bits == 0x12345608);

  // bitwise not on signed integers
  assert(~(-2) == 1);
  assert(~0 == -1);
}

[[rc::returns("{0} @ int<i32>")]]
int test_comma(){
  int x = (NULL, 42);

  return x + x, x - x;
}

[[rc::global("{1} @ int<i32>")]]
int global;

[[rc::inlined]]
int inline_global1() {
  return global;
}

[[rc::requires("[initialized \"global\" ()]")]]
[[rc::returns("{1} @ int<i32>")]]
int inline_global2() {
  return inline_global1();
}
