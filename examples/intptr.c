#include <refinedc.h>
#include <stdint.h>
#include <stddef.h>

//@rc::inlined
//@Notation "P ? l : r" :=
//@  (if bool_decide P then l else r)
//@  (at level 100, l at next level, r at next level).
//@rc::end

/**** Casting a pointer to an integer ***************************************/

// Cast a pointer to an integer, keeping the provenance.
[[rc::parameters("l : loc")]]
[[rc::args("l @ &own<int<i32>>")]]
[[rc::returns("l @ intptr<uintptr_t>")]]
uintptr_t int_ptr1(int* p){
  uintptr_t i = (uintptr_t) p;
  // return (i + 0); ← Does not work (provenance dropped by arithmetic).
  return i;
}

// Cast a pointer to an integer, but losing the provenance.
[[rc::parameters("l : loc")]]
[[rc::args("l @ &own<int<i32>>")]]
[[rc::returns("{l.2} @ int<uintptr_t>")]]
uintptr_t int_ptr2(int* p){
  uintptr_t i = (uintptr_t) p;
  return i;
}

// Cast a pointer to an integer, but losing the provenance.
[[rc::parameters("l : loc")]]
[[rc::args("l @ &own<int<i32>>")]]
[[rc::returns("{l.2} @ int<uintptr_t>")]]
uintptr_t int_ptr3(int* p){
  uintptr_t i = (uintptr_t) p;
  return i + 0; // ← We can do arithmetic (provenance not required).
}

// Weird function working on integers obtained from pointers.
[[rc::parameters("p1 : loc", "p2 : loc")]]
[[rc::args("p1 @ &own<int<i32>>", "p2 @ &own<int<i32>>")]]
[[rc::returns("{p1.2 `min` p2.2} @ int<uintptr_t>")]]
uintptr_t min_ptr_val1(int *p1, int *p2){
  uintptr_t i1 = (uintptr_t) p1;
  uintptr_t i2 = (uintptr_t) p2;

  if(i1 <= i2){
    return i1;
  }

  return i2;
}

// The same but keeping the provenance.
[[rc::parameters("p1 : loc", "p2 : loc")]]
[[rc::args("p1 @ &own<int<i32>>", "p2 @ &own<int<i32>>")]]
[[rc::returns("{p1.2 ≤ p2.2 ? p1 : p2} @ intptr<uintptr_t>")]]
uintptr_t min_ptr_val2(int *p1, int *p2){
  uintptr_t i1 = (uintptr_t) p1;
  uintptr_t i2 = (uintptr_t) p2;

  if(i1 <= i2){
    return i1;
  }

  return i2;
}

/**** Casting an integer to a pointer ***************************************/

// Simple roundtrip cast.
[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<int<i32>>")]]
[[rc::returns("p @ &own<place<p>>")]]
int* roundtrip1(int* p){
  uintptr_t i = (uintptr_t) p;
  void *q = (void*) i; // ← The provenance transfered back.
  return q;
}

// Roundtrip cast with dummy arithmetic.
[[rc::parameters("p : loc")]]
[[rc::args("p @ &own<int<i32>>")]]
[[rc::exists("id : {option alloc_id}")]] // ← Only ∃ on provenance.
[[rc::returns("{(id, p.2)} @ &own<place<{(id, p.2)}>>")]]
int* roundtrip2(int* p){
  uintptr_t i = (uintptr_t) p;
  void *q = (void*) (i + 0); // ← The provenance is lost here.
  return q;
}

// Roundtrip cast with dummy arithmetic and provenance recovery.
[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("p @ &own<n @ int<i32>>")]]
int* roundtrip3(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = (void*) (i + 0); // ← The provenance is lost here.
  return rc_copy_alloc_id(q, p); // ← Copy provenance from [p].
}

// Roundrip cast with flow of ownership.
[[rc::parameters("l : loc", "n : Z")]]
[[rc::args("l @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own l : n @ int<i32>")]]
int roundtrip_and_read1(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = (int*) i;
  int r = *q;
  return r;
}

// Roundrip cast with flow of ownership and provenance recovery.
[[rc::parameters("l : loc", "n : Z")]]
[[rc::args("l @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own l : n @ int<i32>")]]
int roundtrip_and_read2(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = (int*) (i * 1);
  q = rc_copy_alloc_id(q, p);
  int r = *q;
  return r;
}

// Small variation in syntax (for testing).
[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own p : n @ int<i32>")]]
int roundtrip_and_read3(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = rc_copy_alloc_id((int*) (i * 1), p);
  return *q;
}

// Another variant of the same example.
[[rc::parameters("p : loc", "n : Z")]]
[[rc::args("p @ &own<n @ int<i32>>")]]
[[rc::returns("n @ int<i32>")]]
[[rc::ensures("own p : n @ int<i32>")]]
int roundtrip_and_read4(int* p){
  uintptr_t i = (uintptr_t) p;
  int *q = (int*) (i * 1);
  return *(rc_copy_alloc_id(q, p));
}

// Copy the provenance from an int.
[[rc::parameters("p : loc")]]
[[rc::args("p @ intptr<uintptr_t>")]]
[[rc::requires("[alloc_alive_loc p]", "[loc_in_bounds p 0]")]] // TODO: get rid of the loc_in_bounds sidecondition
[[rc::returns("p @ &own<place<p>>")]]
[[rc::ensures("[alloc_alive_loc p]")]]
void* int_to_ptr(uintptr_t p){
  void *q = (void*) (p * 1);
  return (rc_copy_alloc_id(q, p));
}
