From refinedc.typing Require Import typing.
From refinedc.examples.misc Require Import shift_code.
Set Default Proof Using "Type".

(* Generated from [theories/examples/misc/shift.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [times_two]. *)
  Definition type_of_times_two :=
    fn(∀ x : nat; (x @ (int (u32))); ⌜2 * x < it_max u32⌝)
      → ∃ () : (), ((2 * x) @ (int (u32))); True.

  (* Specifications for function [div_two]. *)
  Definition type_of_div_two :=
    fn(∀ x : nat; (x @ (int (u32))); True)
      → ∃ () : (), ((x `div` 2) @ (int (u32))); True.
End spec.
