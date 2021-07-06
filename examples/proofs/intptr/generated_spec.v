From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Notation "P ? l : r" :=
    (if bool_decide P then l else r)
    (at level 100, l at next level, r at next level).

  (* Type definitions. *)

  (* Specifications for function [int_ptr1]. *)
  Definition type_of_int_ptr1 :=
    fn(∀ l : loc; (l @ (&own (int (i32)))); True)
      → ∃ () : (), (l @ (intptr (uintptr_t))); True.

  (* Specifications for function [int_ptr2]. *)
  Definition type_of_int_ptr2 :=
    fn(∀ l : loc; (l @ (&own (int (i32)))); True)
      → ∃ () : (), ((l.2) @ (int (uintptr_t))); True.

  (* Specifications for function [int_ptr3]. *)
  Definition type_of_int_ptr3 :=
    fn(∀ l : loc; (l @ (&own (int (i32)))); True)
      → ∃ () : (), ((l.2) @ (int (uintptr_t))); True.

  (* Specifications for function [min_ptr_val1]. *)
  Definition type_of_min_ptr_val1 :=
    fn(∀ (p1, p2) : loc * loc; (p1 @ (&own (int (i32)))), (p2 @ (&own (int (i32)))); True)
      → ∃ () : (), ((p1.2 `min` p2.2) @ (int (uintptr_t))); True.

  (* Specifications for function [min_ptr_val2]. *)
  Definition type_of_min_ptr_val2 :=
    fn(∀ (p1, p2) : loc * loc; (p1 @ (&own (int (i32)))), (p2 @ (&own (int (i32)))); True)
      → ∃ () : (), ((p1.2 ≤ p2.2 ? p1 : p2) @ (intptr (uintptr_t))); True.

  (* Specifications for function [pointer_to_integer_comp_det]. *)
  Definition type_of_pointer_to_integer_comp_det :=
    fn(∀ () : (); True) → ∃ () : (), (void); (True).

  (* Specifications for function [roundtrip1]. *)
  Definition type_of_roundtrip1 :=
    fn(∀ p : loc; (p @ (&own (int (i32)))); True)
      → ∃ () : (), (p @ (&own (place (p)))); True.

  (* Specifications for function [roundtrip2]. *)
  Definition type_of_roundtrip2 :=
    fn(∀ p : loc; (p @ (&own (int (i32)))); True)
      → ∃ id : prov, (((id, p.2)) @ (&own (place ((id, p.2))))); True.

  (* Specifications for function [roundtrip3]. *)
  Definition type_of_roundtrip3 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (p @ (&own (n @ (int (i32))))); True.

  (* Specifications for function [roundtrip_and_read1]. *)
  Definition type_of_roundtrip_and_read1 :=
    fn(∀ (l, n) : loc * Z; (l @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (l ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read2]. *)
  Definition type_of_roundtrip_and_read2 :=
    fn(∀ (l, n) : loc * Z; (l @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (l ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read3]. *)
  Definition type_of_roundtrip_and_read3 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read4]. *)
  Definition type_of_roundtrip_and_read4 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read_past_the_end]. *)
  Definition type_of_roundtrip_and_read_past_the_end :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [roundtrip_and_read_past_the_end_copy_alloc_id]. *)
  Definition type_of_roundtrip_and_read_past_the_end_copy_alloc_id :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [cast_NULL]. *)
  Definition type_of_cast_NULL :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.
End spec.
