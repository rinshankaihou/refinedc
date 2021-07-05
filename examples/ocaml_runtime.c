#include <refinedc.h>
#include <stdint.h>
#include <stdbool.h>
#include <stddef.h>

// "Native integer" types (defined in [caml/config.h].
typedef int64_t intnat;
typedef uint64_t uintnat;

// A value either represents:
// - an encoded integer (long),
// - an encoded pointer to a "block" (points to the first field),
// - a naked pointer (deprecated), pointing outside the OCaml heap.
/* typedef intnat value; */
typedef uintnat value;

// Longs vs blocks.
#define Is_long(x)   (((x) & 1) != 0)
#define Is_block(x)  (((x) & 1) == 0)

//@rc::inlined
//@  Definition ocaml_value (b:bool) : type :=
//@    tyexists (λ p, b @ optional (p.1 @ intptr i64) (p.2 @ int i64))%I.
//@   Global Program Instance optionable_intptr_int l i it :
//@    Optionable (l @ intptr it) (i @ int it) (IntOp it) (IntOp it) := {|
//@    opt_pre _ _ := False%I;
//@  |}.
//@  Next Obligation. done. Qed.
//@  Next Obligation. iIntros (????????? ?). done. Qed.
//@rc::end

/* [[rc::parameters("b : bool")]] */
/* [[rc::args("ocaml_value<b>")]] */
/* [[rc::returns("b @ boolean<bool_it>")]] */
/* bool Is_long(value x) { return (((x) & 1) != 0); } */
/* bool Is_block(value x) { return (((x) & 1) == 0); } */

// Conversion from/to a Long (name format used everywhere: "to_from").
/* #define Val_long(x) ((intnat) (((uintnat)(x) << 1)) + 1) */
#define Val_long(x) ((value) (((uintnat)(x) << 1)) + 1)
#define Long_val(x) ((x) >> 1)

[[rc::requires("{True}")]]
[[rc::tactics("all: try by rewrite (Z.land_ones _ 1) //; apply Z.mod_divide; [done| etrans; [|done]]; solve_goal.")]]
void client(){
  unsigned long large_int = 0xdeadbeef;
  unsigned int  small_int = 42;

  value v1 = (value) &large_int;
  value v2 = Val_long(small_int);

  assert(Is_block(v1));
  assert(Is_long(v2));

  unsigned long *large_int_ptr = (unsigned long *) v1;
  assert(Long_val(v2) == 42);
  assert(*large_int_ptr == 0xdeadbeef);
}