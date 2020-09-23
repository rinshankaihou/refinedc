From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sfree_tree.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sfree_tree]. *)
  Lemma type_sfree_tree (free_tree : loc) :
    free_tree ◁ᵥ free_tree @ function_ptr type_of_free_tree -∗
    typed_function (impl_sfree_tree free_tree) type_of_sfree_tree.
  Proof.
    start_function "sfree_tree" (p) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sfree_tree" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "sfree_tree".
  Qed.
End proof_sfree_tree.
