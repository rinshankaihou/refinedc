From refinedc.typing Require Import typing.
From refinedc.examples.quick_sort Require Import generated_code.
From refinedc.examples.quick_sort Require Import generated_spec.
From refinedc.examples.quick_sort Require Import quick_sort_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/quick_sort.c]. *)
Section proof_qsort.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [qsort]. *)
  Lemma type_qsort (global_partition global_qsort : loc) :
    global_partition ◁ᵥ global_partition @ function_ptr type_of_partition -∗
    global_qsort ◁ᵥ global_qsort @ function_ptr type_of_qsort -∗
    typed_function (impl_qsort global_partition global_qsort) type_of_qsort.
  Proof.
    Open Scope printing_sugar.
    start_function "qsort" ([[[a es] lo] hi]) => arg_arr arg_lo arg_hi local_k.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "qsort" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by solve_unchanged.
    all: try by solve_length_by_perm.
    all: try by solve_perm_by_trans.
    all: try by apply: sorted_nil; solve_goal.
    all: try by apply: sorted_qsort; solve_goal.
    all: print_sidecondition_goal "qsort".
  Qed.
End proof_qsort.
