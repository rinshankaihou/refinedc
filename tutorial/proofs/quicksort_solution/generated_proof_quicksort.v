From refinedc.typing Require Import typing.
From refinedc.tutorial.quicksort_solution Require Import generated_code.
From refinedc.tutorial.quicksort_solution Require Import generated_spec.
From refinedc.tutorial.quicksort_solution Require Import list_proofs.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_solution.c]. *)
Section proof_quicksort.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [quicksort]. *)
  Lemma type_quicksort (append partition quicksort : loc) :
    append ◁ᵥ append @ function_ptr type_of_append -∗
    partition ◁ᵥ partition @ function_ptr type_of_partition -∗
    quicksort ◁ᵥ quicksort @ function_ptr type_of_quicksort -∗
    typed_function (impl_quicksort append partition quicksort) type_of_quicksort.
  Proof.
    start_function "quicksort" ([list_l l]) => arg_l local_pivot local_higher.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "quicksort" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try (eapply sorted_append_middle_el => //; [ apply _ | | ]; last first).
    all: repeat list_perm_subst; eauto using filter_permutation, Forall_filter with lia.
    all: print_sidecondition_goal "quicksort".
  Qed.
End proof_quicksort.
