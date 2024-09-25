From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge1 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge1 Require Import generated_spec.
From refinedc.examples.VerifyThis2021.challenge1 Require Import challenge1_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge1.c]. *)
Section proof_next.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [next]. *)
  Lemma type_next :
    ⊢ typed_function impl_next type_of_next.
  Proof.
    Local Open Scope printing_sugar.
    start_function "next" ([A p]) => arg_A arg_size local_i local_temp local_j.
    prepare_parameters (A p).
    split_blocks ((
      <[ "#8" :=
        ∃ Acur : list Z,
        ∃ i : Z,
        ∃ j : Z,
        ∃ s : nat,
        arg_size ◁ₗ ((length A) @ (int (i32))) ∗
        local_temp ◁ₗ uninit (it_layout i32) ∗
        arg_A ◁ₗ (p @ (&own (array (i32) (Acur `at_type` int i32)))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        local_j ◁ₗ (j @ (int (i32))) ∗
        ⌜length Acur = length A⌝ ∗
        ⌜length A <= max_int i32⌝ ∗
        ⌜next_start s A⌝ ∗
        ⌜0 < i <= j + 1⌝ ∗
        ⌜s <= i⌝ ∗
        ⌜j < length A⌝ ∗
        ⌜next_partial_swap s (Z.to_nat i) (Z.to_nat j) Acur A⌝
    ]> $
      <[ "#5" :=
        ∃ Acur : list Z,
        ∃ i : Z,
        ∃ j : Z,
        arg_size ◁ₗ ((length A) @ (int (i32))) ∗
        local_temp ◁ₗ uninit (it_layout i32) ∗
        arg_A ◁ₗ (p @ (&own (array (i32) (Acur `at_type` int i32)))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        local_j ◁ₗ (j @ (int (i32))) ∗
        ⌜length Acur = length A⌝ ∗
        ⌜length A <= max_int i32⌝ ∗
        ⌜0 < i < length A⌝ ∗
        ⌜i <= j < length A⌝ ∗
        ⌜∃ e, next_end (Z.to_nat i) e A ∧ e <= j⌝ ∗
        ⌜next_start (Z.to_nat i) A⌝ ∗
        ⌜Acur = A⌝
    ]> $
      <[ "#1" :=
        ∃ Acur : list Z,
        ∃ i : Z,
        arg_size ◁ₗ ((length A) @ (int (i32))) ∗
        local_temp ◁ₗ uninit (it_layout i32) ∗
        local_j ◁ₗ uninit (it_layout i32) ∗
        arg_A ◁ₗ (p @ (&own (array (i32) (Acur `at_type` int i32)))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        ⌜length Acur = length A⌝ ∗
        ⌜length A <= max_int i32⌝ ∗
        ⌜0 <= i < length A⌝ ∗
        ⌜Sorted Z.ge (drop (Z.to_nat i) A)⌝ ∗
        ⌜Acur = A⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "next" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "next" "#8".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "next" "#5".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "next" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try apply: next_perm_implies_perm.
    all: try by apply: next_perm_end; destruct i.
    all: try by apply: next_perm_next; solve_goal.
    all: try by apply: Sorted_small; solve_goal.
    all: try (apply: NPSStep; try (apply: next_partial_swap_mono;[done|..]); try lia; try done; rewrite Z2Nat.inj_add ?Nat.sub_1_r -?Nat.add_pred_r/= ?Nat.add_0_r ?Nat.succ_pred;[|lia..]).
    all: try (apply: NPSBase => //; try lia; have <-: Z.to_nat j = e; [ by have := next_end_gt (Z.to_nat j) _ _ _ _ _ ltac:(done) ltac:(done) ltac:(done); lia|]).
    all: try by apply: swap_intro.
    all: try by eexists _, _.
    all: try by destruct (decide (i = j)); [ | lia]; subst; have := (next_start_lt _ _ _ _ ltac:(done) ltac:(done) ltac:(done)); lia.
    all: try by eexists _; split; [done|]; destruct (decide (e = Z.to_nat j)); [subst |lia]; change (Z.to_nat 1) with 1%nat in *; revert select (next_end _ _ _) => -[?]; naive_solver lia.
    all: try by erewrite drop_S => //; rewrite Nat.sub_1_r Nat.succ_pred; [|lia]; apply: Sorted_cons => //; erewrite drop_S => //; by constructor.
    all: try by have [//|e ?] := next_end_exists (Z.to_nat i) A _ _ ltac:(done) ltac:(done); eexists _; split; [done| by apply: next_end_upper].
    all: print_sidecondition_goal "next".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "next".
  Qed.
End proof_next.
