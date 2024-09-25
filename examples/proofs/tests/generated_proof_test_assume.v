From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_assume.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_assume]. *)
  Lemma type_test_assume (global_safe_exit : loc) :
    global_safe_exit ◁ᵥ global_safe_exit @ function_ptr type_of_safe_exit -∗
    typed_function (impl_test_assume global_safe_exit) type_of_test_assume.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_assume" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_assume" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_assume".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_assume".
  Qed.
End proof_test_assume.
