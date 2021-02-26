From refinedc.typing Require Import typing.
From refinedc.examples.quick_sort Require Import generated_code.
From refinedc.examples.quick_sort Require Import generated_spec.
From refinedc.examples.quick_sort Require Import quick_sort_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/quick_sort.c]. *)
Section proof_partition.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [partition]. *)
  Lemma type_partition :
    ⊢ typed_function impl_partition type_of_partition.
  Proof.
    Open Scope printing_sugar.
    start_function "partition" ([[[a es] lo] hi]) => arg_arr arg_lo arg_hi local_i local_key local_j.
    split_blocks ((
      <[ "#7" :=
        ∃ i : nat,
        ∃ j : nat,
        ∃ key : Z,
        ∃ ys : list Z,
        arg_lo ◁ₗ (lo @ (int (i32))) ∗
        arg_hi ◁ₗ (hi @ (int (i32))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        local_j ◁ₗ (j @ (int (i32))) ∗
        local_key ◁ₗ (key @ (int (i32))) ∗
        arg_arr ◁ₗ (a @ (&own (array (i32) (ys `at_type` (int i32))))) ∗
        ⌜lo <= i⌝ ∗
        ⌜i <= j⌝ ∗
        ⌜j <= hi⌝ ∗
        ⌜length ys = length es⌝ ∗
        ⌜unchanged lo hi ys es⌝ ∗
        ⌜partitioned lo i j hi key ys⌝ ∗
        ⌜Permutation (<[j:=key]> ys) es⌝
    ]> $
      <[ "#4" :=
        ∃ i : nat,
        ∃ j : nat,
        ∃ key : Z,
        ∃ ys : list Z,
        arg_lo ◁ₗ (lo @ (int (i32))) ∗
        arg_hi ◁ₗ (hi @ (int (i32))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        local_j ◁ₗ (j @ (int (i32))) ∗
        local_key ◁ₗ (key @ (int (i32))) ∗
        arg_arr ◁ₗ (a @ (&own (array (i32) (ys `at_type` (int i32))))) ∗
        ⌜lo <= i⌝ ∗
        ⌜i <= j⌝ ∗
        ⌜j <= hi⌝ ∗
        ⌜length ys = length es⌝ ∗
        ⌜unchanged lo hi ys es⌝ ∗
        ⌜partitioned lo i j hi key ys⌝ ∗
        ⌜Permutation (<[i:=key]> ys) es⌝
    ]> $
      <[ "#1" :=
        ∃ i : nat,
        ∃ j : nat,
        ∃ key : Z,
        ∃ ys : list Z,
        arg_lo ◁ₗ (lo @ (int (i32))) ∗
        arg_hi ◁ₗ (hi @ (int (i32))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        local_j ◁ₗ (j @ (int (i32))) ∗
        local_key ◁ₗ (key @ (int (i32))) ∗
        arg_arr ◁ₗ (a @ (&own (array (i32) (ys `at_type` (int i32))))) ∗
        ⌜lo <= i⌝ ∗
        ⌜i <= j⌝ ∗
        ⌜j <= hi⌝ ∗
        ⌜length ys = length es⌝ ∗
        ⌜unchanged lo hi ys es⌝ ∗
        ⌜partitioned lo i j hi key ys⌝ ∗
        ⌜Permutation (<[i:=key]> ys) es⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "partition" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "partition" "#7".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "partition" "#4".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "partition" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try simpl_insert; try by solve_goal.
    all: try by solve_unchanged.
    all: try by apply: perm_insert_swap; solve_goal.
    all: try by apply: range_forall_empty; solve_goal.
    all: try by apply: range_forall_extend; eauto; econstructor; solve_goal.
    all: try by apply: range_forall_insert; rewrite /elem_of; solve_goal.
    all: try by apply: range_forall_insert; (have ? : i = j by solve_goal); rewrite /elem_of; solve_goal.
    all: print_sidecondition_goal "partition".
  Qed.
End proof_partition.
