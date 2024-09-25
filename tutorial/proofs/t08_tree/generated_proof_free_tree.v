From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_free_tree.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [free_tree]. *)
  Lemma type_free_tree (global_free_tree global_tfree : loc) :
    global_free_tree ◁ᵥ global_free_tree @ function_ptr type_of_free_tree -∗
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    typed_function (impl_free_tree global_free_tree global_tfree) type_of_free_tree.
  Proof.
    Local Open Scope printing_sugar.
    start_function "free_tree" (p) => arg_t.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free_tree" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "free_tree".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "free_tree".
  Qed.
End proof_free_tree.
