From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t8_tree_code.
From refinedc.examples.tutorial Require Import t8_tree_spec.
From refinedc.examples.tutorial Require Import t8_tree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t8_tree.c]. *)
Section proof_tree_max.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tree_max]. *)
  Lemma type_tree_max (tree_max : loc) :
    tree_max ◁ᵥ tree_max @ function_ptr type_of_tree_max -∗
    typed_function (impl_tree_max tree_max) type_of_tree_max.
  Proof.
    start_function "tree_max" ([[[p l] k] r]) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tree_max" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "tree_max".
  Qed.
End proof_tree_max.
