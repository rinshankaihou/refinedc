From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sremove.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sremove]. *)
  Lemma type_sremove (remove : loc) :
    remove ◁ᵥ remove @ function_ptr type_of_remove -∗
    typed_function (impl_sremove remove) type_of_sremove.
  Proof.
    start_function "sremove" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sremove" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: tree_rel_remove; solve_goal.
    all: print_sidecondition_goal "sremove".
  Qed.
End proof_sremove.
