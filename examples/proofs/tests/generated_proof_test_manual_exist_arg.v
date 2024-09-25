From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_manual_exist_arg.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_manual_exist_arg]. *)
  Lemma type_test_manual_exist_arg :
    ⊢ typed_function impl_test_manual_exist_arg type_of_test_manual_exist_arg.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_manual_exist_arg" (i) => arg_i.
    prepare_parameters (i).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_manual_exist_arg" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_manual_exist_arg".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_manual_exist_arg".
  Qed.
End proof_test_manual_exist_arg.
