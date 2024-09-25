From refinedc.typing Require Import typing.
From refinedc.tutorial.lithium Require Import generated_code.
From refinedc.tutorial.lithium Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.lithium Require Import lithium_tutorial.
Set Default Proof Using "Type".

(* Generated from [tutorial/lithium.c]. *)
Section proof_lithium_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [lithium_test]. *)
  Lemma type_lithium_test :
    ⊢ typed_function impl_lithium_test type_of_lithium_test.
  Proof. refine type_lithium_test. Qed.
End proof_lithium_test.
