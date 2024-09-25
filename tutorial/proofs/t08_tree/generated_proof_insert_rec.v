From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_insert_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [insert_rec]. *)
  Lemma type_insert_rec (global_insert_rec global_node : loc) :
    global_insert_rec ◁ᵥ global_insert_rec @ function_ptr type_of_insert_rec -∗
    global_node ◁ᵥ global_node @ function_ptr type_of_node -∗
    typed_function (impl_insert_rec global_insert_rec global_node) type_of_insert_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "insert_rec" ([[p t] k]) => arg_t arg_k.
    prepare_parameters (p t k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "insert_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "insert_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "insert_rec".
  Qed.
End proof_insert_rec.
