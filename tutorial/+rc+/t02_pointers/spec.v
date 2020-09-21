From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [read_int]. *)
  Definition type_of_read_int :=
    fn(∀ (p, n) : loc * Z; (p @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), (n @ (int (i32))); (p ◁ₗ (n @ (int (i32)))).

  (* Specifications for function [use_read_int]. *)
  Definition type_of_use_read_int :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [no_alias]. *)
  Definition type_of_no_alias :=
    fn(∀ (p, q) : loc * loc; (p @ (&own (int (i32)))), (q @ (&own (int (i32)))); True)
      → ∃ () : (), (void); (p ◁ₗ ((1) @ (int (i32)))) ∗ (q ◁ₗ (int (i32))).

  (* Specifications for function [local_vars]. *)
  Definition type_of_local_vars :=
    fn(∀ () : (); (boolean (bool_it)); True) → ∃ () : (), (void); True.

  (* Specifications for function [ptrs]. *)
  Definition type_of_ptrs :=
    fn(∀ p : loc; (boolean (bool_it)), (p @ (&own (int (i32)))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [ptrs2]. *)
  Definition type_of_ptrs2 :=
    fn(∀ p : loc; (boolean (bool_it)), (p @ (&own (int (i32)))); True)
      → ∃ () : (), (void); True.
End spec.
