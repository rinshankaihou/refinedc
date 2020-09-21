#include <stddef.h>
#include <stdbool.h>
#include "../inc/refinedc.h"

/**
   THIS FILE IS WORK IN PROGRESS! PLEASE CONTINUE TO THE NEXT FILE!
 */

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("p @ &own<n @ int<i32>>")]]
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
[[rc::ensures("p @ &own<{1} @ int<i32>>", "q @ &own<int<i32>>")]]
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
        rc_unfold(*p);
    } else {
        dummy = *p;
        rc_unfold(*p);
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
        rc_unfold(*p1);
        *p2;
    } else {
        *p2;
        rc_unfold(*p2);
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
        rc_unfold(*p1);
        *p;
    } else {
        *p;
        **p1;
        rc_unfold(*p1);
    }
}
