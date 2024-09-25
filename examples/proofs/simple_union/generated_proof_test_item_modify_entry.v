From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import generated_code.
From refinedc.examples.simple_union Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section proof_test_item_modify_entry.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_modify_entry]. *)
  Lemma type_test_item_modify_entry :
    ⊢ typed_function impl_test_item_modify_entry type_of_test_item_modify_entry.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_item_modify_entry" ([[i x] k]) => arg_i arg_key local_old_key.
    prepare_parameters (i x k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_modify_entry" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_item_modify_entry".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_item_modify_entry".
  Qed.
End proof_test_item_modify_entry.
