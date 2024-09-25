From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [int_id]. *)
  Definition type_of_int_id :=
    fn(∀ () : (); (int (i32)); True) → ∃ () : (), (int (i32)); True.

  (* Specifications for function [int_id2]. *)
  Definition type_of_int_id2 :=
    fn(∀ n : Z; (n @ (int (i32))); True)
      → ∃ () : (), (n @ (int (i32))); True.

  (* Specifications for function [add1]. *)
  Definition type_of_add1 :=
    fn(∀ n : Z; (n @ (int (i32))); ⌜n + 1 ≤ max_int i32⌝)
      → ∃ () : (), ((n + 1) @ (int (i32))); True.

  (* Specifications for function [min]. *)
  Definition type_of_min :=
    fn(∀ (a, b) : Z * Z; (a @ (int (i32))), (b @ (int (i32))); True)
      → ∃ () : (), ((a `min` b) @ (int (i32))); True.

  (* Specifications for function [looping_add]. *)
  Definition type_of_looping_add :=
    fn(∀ (va, vb) : Z * Z; (va @ (int (i32))), (vb @ (int (i32))); ⌜va + vb ≤ max_int i32⌝ ∗ ⌜0 <= va⌝)
      → ∃ () : (), ((va + vb) @ (int (i32))); True.

  (* Specifications for function [int_ptrs]. *)
  Definition type_of_int_ptrs :=
    fn(∀ (p1, p2) : loc * loc; (p1 @ (&own (int (i32)))), (p2 @ (&own (int (i32)))); True)
      → ∃ () : (), (void); (p1 ◁ₗ (int (i32))) ∗ (p2 ◁ₗ (int (i32))).

  (* Specifications for function [call_int_ptrs]. *)
  Definition type_of_call_int_ptrs :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜True⌝.

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
