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
