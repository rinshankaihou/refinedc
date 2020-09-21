From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sempty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sempty]. *)
  Lemma type_sempty (empty : loc) :
    empty ◁ᵥ empty @ function_ptr type_of_empty -∗
    typed_function (impl_sempty empty) type_of_sempty.
  Proof.
    start_function "sempty" ([]).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sempty" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: LeafRel; solve_goal.
    all: print_sidecondition_goal "sempty".
  Qed.
End proof_sempty.
