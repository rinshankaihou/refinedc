From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_tree_max.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tree_max]. *)
  Lemma type_tree_max (global_tree_max : loc) :
    global_tree_max ◁ᵥ global_tree_max @ function_ptr type_of_tree_max -∗
    typed_function (impl_tree_max global_tree_max) type_of_tree_max.
  Proof.
    Open Scope printing_sugar.
    start_function "tree_max" ([p s]) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tree_max" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: by set_unfold; naive_solver lia.
    all: print_sidecondition_goal "tree_max".
  Qed.
End proof_tree_max.
