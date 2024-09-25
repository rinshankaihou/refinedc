From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t02_ownership Require Import generated_code.
From refinedc.tutorial.VerifyThis.t02_ownership Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t02_ownership.c]. *)
Section proof_test_2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_2]. *)
  Lemma type_test_2 (global_append_2 global_talloc : loc) :
    global_append_2 ◁ᵥ global_append_2 @ function_ptr type_of_append_2 -∗
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_test_2 global_append_2 global_talloc) type_of_test_2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_2" ([]) => local_node1 local_node2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_2".
  Qed.
End proof_test_2.
