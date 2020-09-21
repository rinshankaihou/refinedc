From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init (alloc : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_init alloc) type_of_init.
  Proof.
    start_function "init" (k) => arg_key local_node.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
