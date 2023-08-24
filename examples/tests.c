#include <stddef.h>
#include <stdbool.h>
#include <stdint.h>
#include "refinedc.h"
#include "assume.h"
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
int unreachable();

[[rc::returns("void")]]
void test_ternary(){
  int local = 0;
  assert((2 ? 3 : 2) == 3);
  assert((&local != NULL ? (return1() ? return1() : unreachable()) + 3 : 2) == 4);
}

[[rc::requires("True")]]
int test_assume(){
  assume(false);
  assert(1 == 2);
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

[[rc::returns("void")]]
void test_logical(){
  if ((1 && 2) || 0/0) {
    assert(1);
  } else {
    assert(0);
  }
  assert((1 && 2) == 1 && (2 || 0) == 1);
  if(INT_MAX) { assert(1); } else { assert(0); }
  assert(UINT_MAX);
}

[[rc::returns("void")]]
void test_not_ptr(){
  int i;
  int *pi = &i;

  if(!pi){
    assert(0);
  }

  if(pi){
    assert(1);
  } else {
    assert(0);
  }

  assert(pi);

  void *p = NULL;
  if(p){
    assert(0);
  }

  if(!p){
    assert(1);
  } else {
    assert(0);
  }

  assert(!p);
}

[[rc::returns("{0} @ int<i32>")]]
int main(){
  // Check that [return 0] is inserted corectly.
}

struct test { int a; };

[[rc::exists("n : Z")]]
[[rc::returns("struct<struct_test, n @ int<i32>>")]]
[[rc::ensures("{n = 1}")]]
struct test test_struct_return() {
  struct test test;
  test.a = 1;
  return test;
}

typedef void (*test_fn)(void);

[[rc::parameters("spec : {unit → fn_params}")]]
[[rc::args("function_ptr<spec>")]]
[[rc::returns("function_ptr<spec>")]]
test_fn test_fn_params(test_fn f) {
    return f;
}

struct [[rc::parameters("z: Z", "n : Z")]] [[rc::refined_by("x: unit")]] test2 {
  [[rc::field("z @ int<i32>")]]
  int a;
  [[rc::field("&own<test2<n, z>>")]]
  struct test2 * next;
};

[[rc::parameters("z : Z", "n : Z")]]
[[rc::args("test2<z, n>")]]
[[rc::returns("z @ int<i32>")]]
int test_struct2(struct test2 s) {
  return s.a;
}

[[rc::returns("{0xf1} @ int<i32>")]]
int test_reduce() {
  return rc_reduce_expr((1 | 0xff0) & 0xff);
}

[[rc::returns("{0} @ int<i32>")]]
int test_conditional_annot() {
  /* unsigned short i = rc_annot_expr((unsigned short) 0, "a"); */
  unsigned short i2 = 0 ? (unsigned short) 0 : (unsigned short) 0;
  return i2;
}


[[rc::parameters("i : Z")]]
[[rc::args("i @ int<i32>")]]
[[rc::returns("i @ int<i32>")]]
int test_rc_assert(i) {
  // test that we don't loose information through the rc::exists in rc_assert
  [[rc::exists("j : Z")]]
  [[rc::inv_vars("i : j @ int<i32>")]]
  rc_assert;

  // test two exists
  [[rc::exists("j : Z", "k : Z")]]
  [[rc::inv_vars("i : j @ int<i32>")]]
  [[rc::constraints("{k = j}")]]
  rc_assert;
  return i;
}


[[rc::parameters("n : Z", "m : Z", "o : {option Z}")]]
[[rc::args("n @ int<i32>", "m @ int<i32>",
           "{m = 1} @ optional<&own<int<i32>>, null>",
           "o @ optionalO<λ x. &own<x @ int<i32>>, null>")]]
// comment to test printing of case distinctions
[[rc::trust_me]]
void test_case_printing(int n, int m, int *p1, int *p2) {
  // the comments in each case show the expected printing
  // this is missing the union case distinction, can be tested in simple_union.c
  switch (n) {
  // type_switch_int
  case 1:
    // Case distinction (case 1)
    rc_stop(n);

  // type_if_int
  case 2:
    // Case distinction (if 1 ≠ 0) -> true
    if (1) {}
    rc_stop(n);
  case 3:
    // Case distinction (if m ≠ 0) -> true
    // Case distinction (if m ≠ 0) -> false // TODO, currently (if 0 ≠ 0) -> false
    if (m) {}
    rc_stop(n);

  // type_if_generic_boolean
  case 4:
    // TODO: Should this show up?
    // Case distinction (if bool_decide (1 = 1)) -> true // TODO, currently (if true) -> true
    if (1 == 1) {}
    rc_stop(n);
  case 5:
    // Case distinction (if bool_decide (m = 1)) -> true // TODO, currently (if true) -> true
    // Case distinction (if bool_decide (m = 1)) -> false
    if (m == 1) {}
    rc_stop(n);

  // type_eq_optional_refined
  case 6:
    // TODO: Should also trivial if case distinctions show up here?
    // Case distinction (optional == ... : m = 1) // TODO, currently (optional == ... : 1 = 1)
    // Case distinction (optional == ... : m ≠ 1)
    if (p1 == NULL) {}
    rc_stop(n);

  // type_neq_optional
  case 7:
    // TODO: Should also trivial if case distinctions show up here?
    // Case distinction (optional != ... : m = 1) // TODO, currently (optional != ... : 1 = 1)
    // Case distinction (optional != ... : m ≠ 1)
    if (p1 != NULL) {}
    rc_stop(n);

  // type_eq_optionalO
  case 8:
    // TODO: Should also trivial if case distinctions show up here?
    // Case distinction TraceOptionalO -> (Some z)
    // Case distinction TraceOptionalO -> None
    if (p2 == NULL) {}
    rc_stop(n);

  // type_neq_optional
  case 9:
    // TODO: Should also trivial if case distinctions show up here?
    // Case distinction TraceOptionalO -> (Some z)
    // Case distinction TraceOptionalO -> None
    if (p2 != NULL) {}
    rc_stop(n);

  // type_switch_int
  default:
    // Case distinction (default)
    rc_stop(n);
  }
}
