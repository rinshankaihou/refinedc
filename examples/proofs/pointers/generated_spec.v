From refinedc.typing Require Import typing.
From refinedc.examples.pointers Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

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
    fn(∀ () : (); (builtin_boolean); True) → ∃ () : (), (void); True.

  (* Specifications for function [ptrs]. *)
  Definition type_of_ptrs :=
    fn(∀ p : loc; (builtin_boolean), (p @ (&own (int (i32)))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [ptrs2]. *)
  Definition type_of_ptrs2 :=
    fn(∀ p : loc; (builtin_boolean), (p @ (&own (int (i32)))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [ptr_id]. *)
  Definition type_of_ptr_id :=
    fn(∀ (p, ty) : loc * type; (p @ (&own (ty))), (int (i32)); True)
      → ∃ () : (), (p @ (&own (ty))); True.

  (* Specifications for function [ptr_id_test]. *)
  Definition type_of_ptr_id_test :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜True⌝.
End spec.
