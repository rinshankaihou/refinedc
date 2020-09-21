From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_code spinlock_def spinlock_proof.
From refinedc.examples.latch Require Import latch_code latch_def latch_proof_latch_release latch_proof_latch_wait.
From refinedc.examples.tutorial Require Import t3_list_code t4_alloc_code t5_main_code.
From refinedc.examples.tutorial Require Import t3_list_spec t4_alloc_spec t5_main_spec.
From refinedc.examples.tutorial Require Import t5_main_proof_main t5_main_proof_main2 t4_alloc_proof_init_alloc t4_alloc_proof_alloc t4_alloc_proof_free t3_list_proof_test t3_list_proof_reverse t3_list_proof_pop t3_list_proof_push t3_list_proof_is_empty t3_list_proof_init t3_list_proof_member.
From refinedc.typing Require Import adequacy.
(* Set Default Proof Using "Type". *)


Section adequate.
  Context (block_allocator_data block_allocator_state block_initialized : Z).
  Let loc_allocator_data := block_to_loc block_allocator_data.
  Let loc_allocator_state := block_to_loc block_allocator_state.
  Let loc_initialized := block_to_loc block_initialized.
  Context (loc_sl_init loc_sl_lock loc_sl_unlock
           loc_latch_wait loc_latch_release
           loc_init loc_is_empty loc_push loc_pop loc_member loc_reverse loc_test
           loc_alloc loc_free loc_init_alloc
           loc_main loc_main2 : loc).
  Context (Hlayout_alloc_state : loc_allocator_state `has_layout_loc` struct_alloc_state).
  Context (Hlayout_initialized : loc_initialized `has_layout_loc` struct_latch).
  Definition functions  : list function := [
    impl_sl_init; impl_sl_lock; impl_sl_unlock;

    impl_latch_wait; impl_latch_release;

    impl_init; impl_is_empty; impl_push loc_alloc; impl_pop loc_free; impl_member; impl_reverse;
    impl_test loc_alloc loc_free loc_init loc_is_empty loc_push loc_pop loc_reverse loc_member;

    impl_alloc loc_allocator_state loc_sl_lock loc_sl_unlock;
    impl_free loc_allocator_state loc_sl_lock loc_sl_unlock;
    impl_init_alloc loc_allocator_state loc_sl_init;

    impl_main loc_initialized loc_allocator_data loc_test loc_free loc_init_alloc loc_latch_release;
    impl_main2 loc_initialized loc_test loc_latch_wait
  ].
  Definition function_locs : list loc := [
    loc_sl_init; loc_sl_lock; loc_sl_unlock;

    loc_latch_wait; loc_latch_release;

    loc_init; loc_is_empty; loc_push; loc_pop; loc_member; loc_reverse; loc_test;

    loc_alloc; loc_free; loc_init_alloc;

    loc_main; loc_main2
  ].

  Definition initial_heap : gmap Z (list mbyte) :=
    <[block_allocator_data := replicate (Z.to_nat 10000) Poison ]> $
    <[block_allocator_state := replicate (struct_alloc_state).(ly_size) Poison ]> $
    <[block_initialized := LATCH_INIT ]> $
    ∅.

  Definition global_locs : gmap string loc :=
    <["allocator_data" := loc_allocator_data]> $
    <["allocator_state" := loc_allocator_state]> $
    <["initialized" := loc_initialized]> $
    ∅.
  Definition global_types `{!typeG Σ} `{!lockG Σ} : gmap string global_type :=
    <["allocator_state" := GT unit (λ '(), t4_alloc_spec.alloc_state)]> $
    (* We need to use initialized_raw to avoid a cyclic definition of globalG  *)
    <["initialized" := GT unit (λ '(), latch (initialized_raw "allocator_state" () (Some loc_allocator_state) (Some (GT unit (λ '(), t4_alloc_spec.alloc_state)))))]> $
    ∅.


  Lemma tutorial_adequate n κs t2 σ2:
    NoDup [block_allocator_data; block_allocator_state; block_initialized] →
    NoDup function_locs →
    nsteps (Λ := stmt_lang) n (initial_thread_state <$> [loc_main; loc_main2],
                               initial_state (fn_lists_to_fns function_locs functions)
                                             (heap_list_to_heap initial_heap)) κs (t2, σ2) →
    ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
  Proof.
    move => HNDblocks HNDfns.

    set Σ : gFunctors := #[typeΣ; lockΣ].
    (* TODO: is there a nicer way to do this? *)
    change ([initial_thread_state loc_main]) with (initial_thread_state <$> [loc_main]).
    apply: (refinedc_adequacy Σ) => ? //.
    exists global_locs, global_types => Hglobals.
    iIntros "Hmt Hfn".

    move: HNDblocks => /NoDup_cons[?/NoDup_cons[? _]].
    iDestruct (heap_list_to_heap_insert with "Hmt") as "[Hdata Hmt]"; [rewrite !lookup_insert_ne //; set_solver|].
    iDestruct (heap_list_to_heap_insert with "Hmt") as "[Hstate Hmt]"; [rewrite !lookup_insert_ne //; set_solver|].
    iDestruct (heap_list_to_heap_insert with "Hmt") as "[Hinit Hmt]"; [done|].
    iClear "Hmt".

    have Hin := I.
    repeat (
        move: {Hin} HNDfns => /NoDup_cons[Hin HNDfns];
        iDestruct (fn_lists_to_fns_cons with "Hfn") as "[#? Hfn]" => //
    ).

    iAssert (
        typed_function (functions !!! 16%nat) type_of_main2 ∗
        typed_function (functions !!! 15%nat) type_of_main ∗
        typed_function (functions !!! 14%nat) type_of_init_alloc ∗
        typed_function (functions !!! 13%nat) type_of_free ∗
        typed_function (functions !!! 12%nat) type_of_alloc ∗
        typed_function (functions !!! 11%nat) type_of_test ∗
        typed_function (functions !!! 10%nat) type_of_reverse ∗
        typed_function (functions !!! 9%nat) type_of_member ∗
        typed_function (functions !!! 8%nat) type_of_pop ∗
        typed_function (functions !!! 7%nat) type_of_push ∗
        typed_function (functions !!! 6%nat) type_of_is_empty ∗
        typed_function (functions !!! 5%nat) type_of_init ∗
        typed_function (functions !!! 4%nat) type_of_latch_release ∗
        typed_function (functions !!! 3%nat) type_of_latch_wait ∗
        typed_function (functions !!! 2%nat) type_of_sl_unlock ∗
        typed_function (functions !!! 1%nat) type_of_sl_lock ∗
        typed_function (functions !!! 0%nat) type_of_sl_init
      )%I as "(Hmain2&Hmain&_)". {
      simpl.
      iLöb as "IH". iDestruct "IH" as "(?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?&?)".
      repeat iSplit.
      - iApply type_main2 => //; iExists _; repeat iSplit => //.
      - iApply type_main => //; iExists _; repeat iSplit => //.
      - iApply type_init_alloc => //; iExists _; repeat iSplit => //.
      - iApply type_free => //; iExists _; repeat iSplit => //.
      - iApply type_alloc => //; iExists _; repeat iSplit => //.
      - iApply type_test => //; iExists _; repeat iSplit => //.
      - iApply type_reverse => //; iExists _; repeat iSplit => //.
      - iApply type_member => //; iExists _; repeat iSplit => //.
      - iApply type_pop => //; iExists _; repeat iSplit => //.
      - iApply type_push => //; iExists _; repeat iSplit => //.
      - iApply type_is_empty => //; iExists _; repeat iSplit => //.
      - iApply type_init => //; iExists _; repeat iSplit => //.
      - iApply type_latch_release => //; iExists _; repeat iSplit => //.
      - iApply type_latch_wait => //; iExists _; repeat iSplit => //.
      - iApply type_sl_unlock => //; iExists _; repeat iSplit => //.
      - iApply type_sl_lock => //; iExists _; repeat iSplit => //.
      - iApply type_sl_init => //; iExists _; repeat iSplit => //.
    }
    iMod (latch_init with "Hinit") as "#Hinit" => //.
    iModIntro. iSplitL => //. 2: iSplitL => //.
    all: iExists _; iSplitR; [iExists _; repeat iSplit => // |].
    - iSplitR. 2: iSplitL "Hstate".
      + iApply initialized_intro => //=. iExists eq_refl => /=. iApply "Hinit".
      + iExists _; iSplit => //; iExists _; iEval (simpl).
        iFrame "Hstate" => //.
      + iExists _; iSplit => //; iExists _; iEval (simpl). iFrame "Hdata" => //.
    - iApply initialized_intro => //=. iExists eq_refl => /=. iApply "Hinit".
  Qed.
End adequate.

(* Print Assumptions tutorial_adequate. *)
