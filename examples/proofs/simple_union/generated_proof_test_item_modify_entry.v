From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import generated_code.
From refinedc.examples.simple_union Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/simple_union.c]. *)
Section proof_test_item_modify_entry.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_modify_entry]. *)
  Lemma type_test_item_modify_entry :
    ⊢ typed_function impl_test_item_modify_entry type_of_test_item_modify_entry.
  Proof.
    start_function "test_item_modify_entry" ([[i x] k]) => arg_i arg_key local_old_key.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_modify_entry" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_item_modify_entry".
  Qed.
End proof_test_item_modify_entry.
