From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import generated_code.
From refinedc.examples.simple_union Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section proof_test_item_set_entry.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_set_entry]. *)
  Lemma type_test_item_set_entry :
    ⊢ typed_function impl_test_item_set_entry type_of_test_item_set_entry.
  Proof.
    start_function "test_item_set_entry" ([[i k] ty]) => arg_i arg_key arg_val.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_set_entry" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test_item_set_entry".
  Qed.
End proof_test_item_set_entry.
