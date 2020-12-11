From refinedc.typing Require Import typing.
From refinedc.tutorial.quicksort_solution Require Import generated_code.
From refinedc.tutorial.quicksort_solution Require Import generated_spec.
From refinedc.tutorial.quicksort_solution Require Import list_proofs.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_solution.c]. *)
Section proof_partition.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [partition]. *)
  Lemma type_partition (global_partition : loc) :
    global_partition ◁ᵥ global_partition @ function_ptr type_of_partition -∗
    typed_function (impl_partition global_partition) type_of_partition.
  Proof.
    start_function "partition" ([[p xs] z]) => arg_l arg_pivot local_rest local_head.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "partition" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite filter_cons; solve_goal.
    all: print_sidecondition_goal "partition".
  Qed.
End proof_partition.
