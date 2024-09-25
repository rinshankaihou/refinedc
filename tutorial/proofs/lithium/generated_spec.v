From refinedc.typing Require Import typing.
From refinedc.tutorial.lithium Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/lithium.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [lithium_test]. *)
  Definition type_of_lithium_test :=
    fn(∀ n : Z; ((n <> 0) @ (optional (&own (n @ (int (i32)))) (null))); True)
      → ∃ () : (), (n @ (int (i32))); True.
End spec.
