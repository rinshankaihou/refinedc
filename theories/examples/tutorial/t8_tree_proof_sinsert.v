From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t8_tree_code.
From refinedc.examples.tutorial Require Import t8_tree_spec.
From refinedc.examples.tutorial Require Import t8_tree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t8_tree.c]. *)
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
