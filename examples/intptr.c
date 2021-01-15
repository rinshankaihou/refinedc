#include <refinedc.h>
#include <stdint.h>
#include <stddef.h>

[[rc::args("&own<int<i32>>")]]
[[rc::returns("int<size_t>")]]
size_t int_ptr(int* p){
  size_t i = (size_t) p;
  return i;
}

[[rc::parameters("p1 : loc", "p2 : loc")]]
[[rc::args("p1 @ &own<int<i32>>", "p2 @ &own<int<i32>>")]]
[[rc::returns("{p1.2 `min` p2.2} @ int<size_t>")]]
size_t min_ptr_val(int *p1, int *p2){
  size_t i1 = (size_t) p1;
  size_t i2 = (size_t) p2;

  if(i1 <= i2){
    return i1;
  }

  return i2;
}

[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<int<i32>>")]]
[[rc::returns("{(None, p.2)} @ &own<place<{(None, p.2)}>>")]]
int* roundtrip1(int* p){
  size_t i = (size_t) p;
  void *q = (void*) i;
  return q;
}

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("p @ &own<n @ int<i32>>")]]
int* roundtrip2(int* p){
  size_t i = (size_t) p;
  int *q = (void*) i;
  return rc_copy_alloc_id(q, p);
}

[[rc::parameters("l : loc", "n : Z")]]
[[rc::args("l @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own l : n @ int<i32>")]]
int roundtrip_and_read(int* p){
  size_t i = (size_t) p;
  int *q = (int*) i;
  q = rc_copy_alloc_id(q, p);
  int r = *q;
  return r;
}

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own p : n @ int<i32>")]]
int roundtrip_and_read2(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = rc_copy_alloc_id((int*) i, p);
  return *q;
}

[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own p : n @ int<i32>")]]
int roundtrip_and_read3(int* p){
  size_t i = (size_t) p;
  int *q = (int*) i;
  return *(rc_copy_alloc_id(q, p));
}
