From refinedc.typing Require Import typing.
From refinedc.examples.ocaml_runtime Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

    Definition ocaml_value (b:bool) : type :=
      tyexists (λ p, b @ optional (p.1 @ intptr i64) (p.2 @ int i64))%I.
     Global Program Instance optionable_intptr_int l i it :
      Optionable (l @ intptr it) (i @ int it) (IntOp it) (IntOp it) := {|
      opt_pre _ _ := False%I;
    |}.
    Next Obligation. done. Qed.
    Next Obligation. iIntros (????????? ?). done. Qed.

  (* Type definitions. *)

  (* Specifications for function [client]. *)
  Definition type_of_client :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.
End spec.
