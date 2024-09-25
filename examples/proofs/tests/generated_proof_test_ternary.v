From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_ternary.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_ternary]. *)
  Lemma type_test_ternary (global_return1 global_unreachable : loc) :
    global_return1 ◁ᵥ global_return1 @ function_ptr type_of_return1 -∗
    global_unreachable ◁ᵥ global_unreachable @ function_ptr type_of_unreachable -∗
    typed_function (impl_test_ternary global_return1 global_unreachable) type_of_test_ternary.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_ternary" ([]) => local_local.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_ternary" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_ternary".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_ternary".
  Qed.
End proof_test_ternary.
