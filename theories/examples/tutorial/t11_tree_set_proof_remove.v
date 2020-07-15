From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t11_tree_set_code.
From refinedc.examples.tutorial Require Import t11_tree_set_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t11_tree_set.c]. *)
Section proof_remove.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [remove]. *)
  Lemma type_remove (free tree_max remove : loc) :
    free ◁ᵥ free @ function_ptr type_of_free -∗
    tree_max ◁ᵥ tree_max @ function_ptr type_of_tree_max -∗
    remove ◁ᵥ remove @ function_ptr type_of_remove -∗
    typed_function (impl_remove free tree_max remove) type_of_remove.
  Proof.
    start_function "remove" ([[p s] k]) => arg_t arg_k local_m local_tmp.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "remove" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try apply Z.le_neq.
    all: try (rewrite difference_union_L !difference_union_distr_l_L !difference_diag_L !difference_disjoint_L; move: (H0 x2) (H1 x2); clear -H9).
    all: try by set_unfold; naive_solver lia.
    all: print_sidecondition_goal "remove".
  Qed.
End proof_remove.
