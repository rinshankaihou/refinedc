From refinedc.typing Require Import typing.
From refinedc.examples.container_of Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/container_of.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [container_of_test]. *)
  Definition type_of_container_of_test :=
    fn(∀ () : (); True) → ∃ () : (), ((4) @ (int (i32))); True.
End spec.
