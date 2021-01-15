From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_node.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [node]. *)
  Lemma type_node (global_alloc : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_node global_alloc) type_of_node.
  Proof.
    Open Scope printing_sugar.
    start_function "node" ([[sl k] sr]) => arg_left arg_key arg_right local_node.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "node" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_solver.
    all: print_sidecondition_goal "node".
  Qed.
End proof_node.
