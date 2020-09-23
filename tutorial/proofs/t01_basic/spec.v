From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [int_id]. *)
  Definition type_of_int_id :=
    fn(∀ () : (); (int (i32)); True) → ∃ () : (), (int (i32)); True.

  (* Specifications for function [int_id2]. *)
  Definition type_of_int_id2 :=
    fn(∀ n : Z; (n @ (int (i32))); True)
      → ∃ () : (), (n @ (int (i32))); True.

  (* Specifications for function [add1]. *)
  Definition type_of_add1 :=
    fn(∀ n : Z; (n @ (int (i32))); ⌜n + 1 < it_max i32⌝)
      → ∃ () : (), ((n + 1) @ (int (i32))); True.

  (* Specifications for function [min]. *)
  Definition type_of_min :=
    fn(∀ (a, b) : Z * Z; (a @ (int (i32))), (b @ (int (i32))); True)
      → ∃ () : (), ((a `min` b) @ (int (i32))); True.

  (* Specifications for function [looping_add]. *)
  Definition type_of_looping_add :=
    fn(∀ (va, vb) : Z * Z; (va @ (int (i32))), (vb @ (int (i32))); ⌜va + vb < it_max i32⌝ ∗ ⌜0 <= va⌝)
      → ∃ () : (), ((va + vb) @ (int (i32))); True.

  (* Specifications for function [init_int]. *)
  Definition type_of_init_int :=
    fn(∀ p : loc; (p @ (&own (uninit (i32)))); True)
      → ∃ () : (), (void); (p ◁ₗ ((1) @ (int (i32)))).

  (* Specifications for function [init_int_test]. *)
  Definition type_of_init_int_test :=
    fn(∀ p : loc; (p @ (&own (uninit (i32)))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [struct_test]. *)
  Definition type_of_struct_test :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_basic)))); True)
      → ∃ () : (), (void); (p ◁ₗ (struct (struct_basic) [@{type} (2) @ (int (i32)) ; (0) @ (int (i32)) ])).
End spec.
