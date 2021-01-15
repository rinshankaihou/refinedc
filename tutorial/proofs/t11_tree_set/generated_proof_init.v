From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init (global_alloc : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_init global_alloc) type_of_init.
  Proof.
    Open Scope printing_sugar.
    start_function "init" (k) => arg_key local_node.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_solver.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
