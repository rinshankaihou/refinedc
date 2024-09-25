From refinedc.typing Require Import typing.
From refinedc.examples.ocaml_runtime Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [client]. *)
  Definition type_of_client :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.
End spec.
