From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_remove.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [remove]. *)
  Lemma type_remove (free remove tree_max : loc) :
    free ◁ᵥ free @ function_ptr type_of_free -∗
    remove ◁ᵥ remove @ function_ptr type_of_remove -∗
    tree_max ◁ᵥ tree_max @ function_ptr type_of_tree_max -∗
    typed_function (impl_remove free remove tree_max) type_of_remove.
  Proof.
    start_function "remove" ([[p t] k]) => arg_t arg_k local_m local_tmp.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "remove" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by case_bool_decide => //; simplify_eq.
    all: print_sidecondition_goal "remove".
  Qed.
End proof_remove.
