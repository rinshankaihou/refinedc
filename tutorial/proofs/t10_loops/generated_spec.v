From refinedc.typing Require Import typing.
From refinedc.tutorial.t10_loops Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t10_loops.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [loop_without_annot]. *)
  Definition type_of_loop_without_annot :=
    fn(∀ () : (); (int (i32)), (int (i32)), (int (i32)); True)
      → ∃ () : (), (void); ⌜True⌝.
End spec.
