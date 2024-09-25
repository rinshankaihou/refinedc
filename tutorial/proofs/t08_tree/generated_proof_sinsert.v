From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sinsert.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sinsert]. *)
  Lemma type_sinsert (global_insert : loc) :
    global_insert ◁ᵥ global_insert @ function_ptr type_of_insert -∗
    typed_function (impl_sinsert global_insert) type_of_sinsert.
  Proof.
    Local Open Scope printing_sugar.
    start_function "sinsert" ([[p s] k]) => arg_t arg_k.
    prepare_parameters (p s k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sinsert" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: tree_rel_insert; solve_goal.
    all: print_sidecondition_goal "sinsert".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "sinsert".
  Qed.
End proof_sinsert.
