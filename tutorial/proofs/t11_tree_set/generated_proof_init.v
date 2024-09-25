From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init (global_talloc : loc) :
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_init global_talloc) type_of_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init" (k) => arg_key local_node.
    prepare_parameters (k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_solver.
    all: print_sidecondition_goal "init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init".
  Qed.
End proof_init.
