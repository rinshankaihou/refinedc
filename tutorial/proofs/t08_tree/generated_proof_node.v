From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_node.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [node]. *)
  Lemma type_node (global_talloc : loc) :
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_node global_talloc) type_of_node.
  Proof.
    Local Open Scope printing_sugar.
    start_function "node" ([[l k] r]) => arg_left arg_key arg_right local_node.
    prepare_parameters (l k r).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "node" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "node".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "node".
  Qed.
End proof_node.
