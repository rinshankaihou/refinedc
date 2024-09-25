From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sfree_tree.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sfree_tree]. *)
  Lemma type_sfree_tree (global_free_tree : loc) :
    global_free_tree ◁ᵥ global_free_tree @ function_ptr type_of_free_tree -∗
    typed_function (impl_sfree_tree global_free_tree) type_of_sfree_tree.
  Proof.
    Local Open Scope printing_sugar.
    start_function "sfree_tree" (p) => arg_t.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sfree_tree" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "sfree_tree".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "sfree_tree".
  Qed.
End proof_sfree_tree.
