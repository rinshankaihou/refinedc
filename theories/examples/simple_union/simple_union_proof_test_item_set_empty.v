From refinedc.typing Require Import typing.
From refinedc.examples.simple_union Require Import simple_union_code.
From refinedc.examples.simple_union Require Import simple_union_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/simple_union/simple_union.c]. *)
Section proof_test_item_set_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_item_set_empty]. *)
  Lemma type_test_item_set_empty :
    ⊢ typed_function impl_test_item_set_empty type_of_test_item_set_empty.
  Proof.
    start_function "test_item_set_empty" (i) => arg_i.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_item_set_empty" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test_item_set_empty".
  Qed.
End proof_test_item_set_empty.
