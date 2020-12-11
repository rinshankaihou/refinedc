From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_free_tree.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [free_tree]. *)
  Lemma type_free_tree (global_free global_free_tree : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_free_tree ◁ᵥ global_free_tree @ function_ptr type_of_free_tree -∗
    typed_function (impl_free_tree global_free global_free_tree) type_of_free_tree.
  Proof.
    start_function "free_tree" (p) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free_tree" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "free_tree".
  Qed.
End proof_free_tree.
