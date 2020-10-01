From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sinsert.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sinsert]. *)
  Lemma type_sinsert (insert : loc) :
    insert ◁ᵥ insert @ function_ptr type_of_insert -∗
    typed_function (impl_sinsert insert) type_of_sinsert.
  Proof.
    start_function "sinsert" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sinsert" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: tree_rel_insert; solve_goal.
    all: print_sidecondition_goal "sinsert".
  Qed.
End proof_sinsert.
