From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
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
    start_function "remove" ([[p t] k]) => arg_t arg_k local_m local_tmp.
    prepare_parameters (p t k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "remove" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by case_bool_decide => //; simplify_eq.
    all: print_sidecondition_goal "remove".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "remove".
  Qed.
End proof_remove.
