From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t03_ownership_and_refinements Require Import generated_code.
From refinedc.tutorial.VerifyThis.t03_ownership_and_refinements Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t03_ownership_and_refinements.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_append global_talloc : loc) :
    global_append ◁ᵥ global_append @ function_ptr type_of_append -∗
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_test global_append global_talloc) type_of_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test" ([]) => local_node1 local_node2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test".
  Qed.
End proof_test.
