From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_remove.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [remove]. *)
  Lemma type_remove (global_remove global_tfree global_tree_max : loc) :
    global_remove ◁ᵥ global_remove @ function_ptr type_of_remove -∗
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    global_tree_max ◁ᵥ global_tree_max @ function_ptr type_of_tree_max -∗
    typed_function (impl_remove global_remove global_tfree global_tree_max) type_of_remove.
  Proof.
    Local Open Scope printing_sugar.
    start_function "remove" ([[p s] k]) => arg_t arg_k local_m local_tmp.
    prepare_parameters (p s k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "remove" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try apply Z.le_neq.
    all: try (rewrite difference_union_L !difference_union_distr_l_L !difference_diag_L !difference_disjoint_L; move: (H0 x2) (H1 x2); clear -H9).
    all: try by set_unfold_trigger; naive_solver (trigger_foralls; lia).
    all: print_sidecondition_goal "remove".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "remove".
  Qed.
End proof_remove.
