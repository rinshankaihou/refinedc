From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_node.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [node]. *)
  Lemma type_node (alloc : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_node alloc) type_of_node.
  Proof.
    start_function "node" ([[l k] r]) => arg_left arg_key arg_right local_node.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "node" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "node".
  Qed.
End proof_node.
