From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import generated_code.
From refinedc.examples.simple_union Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section proof_test_item_set_entry.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_set_entry]. *)
  Lemma type_test_item_set_entry :
    ⊢ typed_function impl_test_item_set_entry type_of_test_item_set_entry.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_item_set_entry" ([[i k] ty]) => arg_i arg_key arg_val.
    prepare_parameters (i k ty).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_set_entry" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_item_set_entry".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_item_set_entry".
  Qed.
End proof_test_item_set_entry.
