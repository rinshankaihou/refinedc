From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t11_tree_set_code.
From refinedc.examples.tutorial Require Import t11_tree_set_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t11_tree_set.c]. *)
Section proof_insert_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [insert_rec]. *)
  Lemma type_insert_rec (node insert_rec : loc) :
    node ◁ᵥ node @ function_ptr type_of_node -∗
    insert_rec ◁ᵥ insert_rec @ function_ptr type_of_insert_rec -∗
    typed_function (impl_insert_rec node insert_rec) type_of_insert_rec.
  Proof.
    start_function "insert_rec" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "insert_rec" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by set_unfold; solve_goal.
    all: print_sidecondition_goal "insert_rec".
  Qed.
End proof_insert_rec.
