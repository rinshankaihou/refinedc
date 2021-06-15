From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import
  generated_code spinlock_def spinlock_proof
  generated_proof_sl_lock generated_proof_sl_unlock.
From refinedc.examples.latch Require Import
  generated_code generated_spec latch_def generated_proof_latch_release
  generated_proof_latch_wait.
From refinedc.tutorial.t03_list Require Import
  generated_code generated_spec generated_proof_test generated_proof_reverse
  generated_proof_pop generated_proof_push generated_proof_is_empty
  generated_proof_init generated_proof_member.
From refinedc.tutorial.t04_alloc Require Import
  generated_code generated_spec generated_proof_init_alloc
  generated_proof_alloc generated_proof_free.
From refinedc.tutorial.t05_main Require Import
  generated_code generated_spec generated_proof_main generated_proof_main2.
From refinedc.typing Require Import adequacy.
(* Set Default Proof Using "Type". *)


Section adequate.
  Context (loc_allocator_data loc_allocator_state loc_initialized : loc).

  Context (addr_sl_init addr_sl_lock addr_sl_unlock
           addr_latch_wait addr_latch_release
           addr_init addr_is_empty addr_push addr_pop addr_member addr_reverse addr_test
           addr_alloc addr_free addr_init_alloc
           addr_main addr_main2 : addr).
  Definition functions  : list function := [
    impl_sl_init; impl_sl_lock; impl_sl_unlock;

    impl_latch_wait; impl_latch_release;

    impl_init; impl_is_empty; impl_push (fn_loc addr_alloc); impl_pop (fn_loc addr_free); impl_member; impl_reverse;
    impl_test (fn_loc addr_alloc) (fn_loc addr_free) (fn_loc addr_init) (fn_loc addr_is_empty) (fn_loc addr_member) (fn_loc addr_pop) (fn_loc addr_push) (fn_loc addr_reverse);

    impl_alloc loc_allocator_state (fn_loc addr_sl_lock) (fn_loc addr_sl_unlock);
    impl_free loc_allocator_state (fn_loc addr_sl_lock) (fn_loc addr_sl_unlock);
    impl_init_alloc loc_allocator_state (fn_loc addr_sl_init);

    impl_main loc_allocator_data loc_initialized (fn_loc addr_free) (fn_loc addr_init_alloc) (fn_loc addr_latch_release) (fn_loc addr_test);
    impl_main2 loc_initialized (fn_loc addr_latch_wait) (fn_loc addr_test)
  ].
  Definition function_addrs : list addr := [
    addr_sl_init; addr_sl_lock; addr_sl_unlock;

    addr_latch_wait; addr_latch_release;

    addr_init; addr_is_empty; addr_push; addr_pop; addr_member; addr_reverse; addr_test;

    addr_alloc; addr_free; addr_init_alloc;

    addr_main; addr_main2
  ].

  Definition initial_heap_locs : list loc := [
    loc_allocator_data;
    loc_allocator_state;
    loc_initialized
  ].
  Definition initial_heap_values : list val.val := [
    replicate (Z.to_nat 10000) MPoison;
    replicate (struct_alloc_state).(ly_size) MPoison;
    LATCH_INIT
  ].

  Definition global_locs : gmap string loc :=
    <["allocator_data" := loc_allocator_data]> $
    <["allocator_state" := loc_allocator_state]> $
    <["initialized" := loc_initialized]> $
    ∅.
  Definition global_types `{!typeG Σ} `{!lockG Σ} : gmap string global_type :=
    <["allocator_state" := GT unit (λ '(),  t04_alloc.generated_spec.alloc_state)]> $
    (* We need to use initialized_raw to avoid a cyclic definition of globalG  *)
    <["initialized" := GT unit (λ '(), (initialized_raw "allocator_state" () (Some loc_allocator_state) (Some (GT unit (λ '(), t04_alloc.generated_spec.alloc_state)))) @ latch )%I]> $
    ∅.


  Ltac unfold_defs :=
    unfold latch.generated_spec.latch_rec, latch_rec.


  Lemma tutorial_adequate n κs t2 σ2 hs σ:
    loc_allocator_data `has_layout_loc` void_ptr →
    loc_allocator_state `has_layout_loc` struct_alloc_state →
    loc_initialized `has_layout_loc` struct_latch →
    (* TODO: Should we try to show that this assumption is provable? *)
    alloc_new_blocks initial_heap_state initial_heap_locs initial_heap_values hs →
    σ = {| st_heap := hs; st_fntbl := fn_lists_to_fns function_addrs functions; |} →
    NoDup function_addrs →
    nsteps (Λ := c_lang) n (initial_prog <$> [(fn_loc addr_main); (fn_loc addr_main2)], σ) κs (t2, σ2) →
    ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
  Proof.
    move => Hly1 Hly2 Hly3 Halloc -> HNDfns.

    set Σ : gFunctors := #[typeΣ; lockΣ].
    apply: (refinedc_adequacy Σ) => //.
    move => ?.
    exists global_locs, global_types => Hglobals.
    iIntros "(Hdata&Hstate&Hinit&_) Hfn".

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
      - adequacy_solve_typed_function type_main2 unfold_defs.
      - adequacy_solve_typed_function type_main unfold_defs.
      - adequacy_solve_typed_function type_init_alloc unfold_defs.
      - adequacy_solve_typed_function type_free unfold_defs.
      - adequacy_solve_typed_function type_alloc unfold_defs.
      - adequacy_solve_typed_function type_test unfold_defs.
      - adequacy_solve_typed_function type_reverse unfold_defs.
      - adequacy_solve_typed_function type_member unfold_defs.
      - adequacy_solve_typed_function type_pop unfold_defs.
      - adequacy_solve_typed_function type_push unfold_defs.
      - adequacy_solve_typed_function type_is_empty unfold_defs.
      - adequacy_solve_typed_function type_init unfold_defs.
      - adequacy_solve_typed_function type_latch_release unfold_defs.
      - adequacy_solve_typed_function type_latch_wait unfold_defs.
      - adequacy_solve_typed_function type_sl_unlock unfold_defs.
      - adequacy_solve_typed_function type_sl_lock unfold_defs.
      - adequacy_solve_typed_function type_sl_init unfold_defs.
    }
    iMod (latch_init with "Hinit") as "#Hinit" => //.
    iModIntro. iSplitL => //. 2: iSplitL => //.
    all: iExists _; iSplitR; [iExists _; repeat iSplit => // |].
    - iSplitR. 2: iSplitL "Hstate".
      + iApply initialized_intro => //=. iExists eq_refl => /=.
        iApply (ty_own_entails with "Hinit").
        repeat adequacy_solve_equiv unfold_defs.
      + iExists _; iSplit => //; iExists _; iEval (simpl).
        rewrite Forall_forall. iFrame "Hstate" => //.
      + iExists _; iSplit => //; iExists _; iEval (simpl).
        rewrite Forall_forall. iFrame "Hdata" => //.
    - iApply initialized_intro => //=. iExists eq_refl => /=.
      iApply (ty_own_entails with "Hinit").
      repeat adequacy_solve_equiv unfold_defs.
  Qed.
End adequate.

(* Print Assumptions tutorial_adequate. *)
