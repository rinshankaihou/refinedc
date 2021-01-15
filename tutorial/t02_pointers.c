#include <stddef.h>
#include <stdbool.h>
#include <refinedc.h>

/**
   THIS FILE IS WORK IN PROGRESS! PLEASE CONTINUE TO THE NEXT FILE!
 */

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own p : n @ int<i32>")]]
int read_int(int *a) {
    return *a;
}

[[rc::returns("void")]]
void use_read_int() {
    int local = 1;
    int read = read_int(&local);
    assert(local == read);
    assert(local == 1);
}

[[rc::parameters("p : loc", "q : loc")]]
[[rc::args("p @ &own<int<i32>>", "q @ &own<int<i32>>")]]
[[rc::ensures("own p : {1} @ int<i32>", "own q : int<i32>")]]
void no_alias(int *a, int *b) {
    int old_b = *b;
    *a = 1;
    assert(*b == old_b);
}

[[rc::args("boolean<bool_it>")]]
void local_vars(bool b) {
    int var = 1, dummy;
    int *p;
    p = &var;
    if(b) {
        dummy = var;
        dummy = *p;
    } else {
        dummy = *p;
        dummy = var;
    }
}

[[rc::parameters("p : loc")]]
[[rc::args("boolean<bool_it>", "p @ &own<int<i32>>")]]
void ptrs(bool b, int *p) {
    int *p1, *p2;
    p1 = p;
    p2 = p;
    if(b) {
        *p1;
        *p2;
    } else {
        *p2;
        *p1;
    }
}

[[rc::parameters("p : loc")]]
[[rc::args("boolean<bool_it>", "p @ &own<int<i32>>")]]
void ptrs2(bool b, int *p) {
    int **p1;
    p1 = &p;
    if(b) {
        **p1;
        *p;
    } else {
        *p;
        **p1;
    }
}

[[rc::parameters("p : loc", "ty : type")]]
[[rc::args("p @ &own<ty>", "int<i32>")]]
[[rc::returns("p @ &own<ty>")]]
void* ptr_id(void *p, int x) {
  return p;
}

[[rc::ensures("True")]]
void ptr_id_test() {
  int x = 1;
  assert(*(int *)ptr_id(&x, 1 + 1) == 1);
}
