From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [test1]. *)
  Definition type_of_test1 :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.
End spec.
