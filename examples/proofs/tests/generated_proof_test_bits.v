From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_bits.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_bits]. *)
  Lemma type_test_bits :
    ⊢ typed_function impl_test_bits type_of_test_bits.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_bits" ([]) => local_selecting_bits local_mask local_clearing_bits local_setting_bits local_a.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_bits" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_bits".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_bits".
  Qed.
End proof_test_bits.
