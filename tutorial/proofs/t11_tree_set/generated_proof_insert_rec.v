From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_insert_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [insert_rec]. *)
  Lemma type_insert_rec (global_insert_rec global_node : loc) :
    global_insert_rec ◁ᵥ global_insert_rec @ function_ptr type_of_insert_rec -∗
    global_node ◁ᵥ global_node @ function_ptr type_of_node -∗
    typed_function (impl_insert_rec global_insert_rec global_node) type_of_insert_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "insert_rec" ([[p s] k]) => arg_t arg_k.
    prepare_parameters (p s k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "insert_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_unfold; (solve_goal || naive_solver lia).
    all: print_sidecondition_goal "insert_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "insert_rec".
  Qed.
End proof_insert_rec.
