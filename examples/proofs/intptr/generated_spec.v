From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [int_ptr]. *)
  Definition type_of_int_ptr :=
    fn(∀ () : (); (&own (int (i32))); True)
      → ∃ () : (), (int (size_t)); True.

  (* Specifications for function [min_ptr_val]. *)
  Definition type_of_min_ptr_val :=
    fn(∀ (p1, p2) : loc * loc; (p1 @ (&own (int (i32)))), (p2 @ (&own (int (i32)))); True)
      → ∃ () : (), ((p1.2 `min` p2.2) @ (int (size_t))); True.

  (* Specifications for function [roundtrip1]. *)
  Definition type_of_roundtrip1 :=
    fn(∀ p : loc; (p @ (&own (int (i32)))); True)
      → ∃ () : (), (((None, p.2)) @ (&own (singleton_place ((None, p.2))))); True.

  (* Specifications for function [roundtrip2]. *)
  Definition type_of_roundtrip2 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (p @ (&own (n @ (int (i32))))); True.

  (* Specifications for function [roundtrip_and_read]. *)
  Definition type_of_roundtrip_and_read :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read2]. *)
  Definition type_of_roundtrip_and_read2 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [roundtrip_and_read3]. *)
  Definition type_of_roundtrip_and_read3 :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).
End spec.
