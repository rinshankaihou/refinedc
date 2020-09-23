From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sinit.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sinit]. *)
  Lemma type_sinit (init : loc) :
    init ◁ᵥ init @ function_ptr type_of_init -∗
    typed_function (impl_sinit init) type_of_sinit.
  Proof.
    start_function "sinit" (k) => arg_key.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sinit" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: NodeRel; try apply LeafRel; set_solver.
    all: print_sidecondition_goal "sinit".
  Qed.
End proof_sinit.
