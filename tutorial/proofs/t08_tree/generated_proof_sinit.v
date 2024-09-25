From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_sinit.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [sinit]. *)
  Lemma type_sinit (global_init : loc) :
    global_init ◁ᵥ global_init @ function_ptr type_of_init -∗
    typed_function (impl_sinit global_init) type_of_sinit.
  Proof.
    Local Open Scope printing_sugar.
    start_function "sinit" (k) => arg_key.
    prepare_parameters (k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sinit" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: NodeRel; try apply LeafRel; set_solver.
    all: print_sidecondition_goal "sinit".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "sinit".
  Qed.
End proof_sinit.
