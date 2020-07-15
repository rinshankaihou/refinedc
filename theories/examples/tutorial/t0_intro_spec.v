From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t0_intro_code.
From refinedc.examples.tutorial Require Import binary_search_defs.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t0_intro.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [binary_search]. *)
  Definition type_of_binary_search :=
    fn(∀ (ls, x, p) : (list Z) * Z * loc; (p @ (&own (array (i32) (ls `at_type` int i32)))), ((length ls) @ (int (i32))), (x @ (int (i32))); ⌜StronglySorted (≤) ls⌝)
      → ∃ () : (), ((x ∈ ls) @ (optional (tyexists (λ i : nat, constrained (i @ (int (i32))) ⌜ls !! i = Some x⌝)) ((-1) @ (int (i32))))); (p ◁ₗ (array (i32) (ls `at_type` int i32))).
End spec.
