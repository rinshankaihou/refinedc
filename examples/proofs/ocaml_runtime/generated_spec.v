From refinedc.typing Require Import typing.
From refinedc.examples.ocaml_runtime Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [client]. *)
  Definition type_of_client :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.
End spec.
