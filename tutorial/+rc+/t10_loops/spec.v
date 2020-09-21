From refinedc.typing Require Import typing.
From refinedc.tutorial.t10_loops Require Import code.
Set Default Proof Using "Type".

(* Generated from [tutorial/t10_loops.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [loop_without_annot]. *)
  Definition type_of_loop_without_annot :=
    fn(∀ () : (); (int (i32)); True) → ∃ () : (), (void); ⌜True⌝.
End spec.
