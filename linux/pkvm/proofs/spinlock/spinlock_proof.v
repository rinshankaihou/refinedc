From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
From refinedc.linux.pkvm.spinlock Require Import generated_spec.
From refinedc.linux.pkvm.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* TODO: figure out if this is what we want and move to type.v *)
Theorem ty_deref_full `{!typeG Σ} (l : loc) (ty : type) `{!Movable ty}:
  l ◁ₗ ty -∗ ∃ v, ⌜l `has_layout_loc` ty_layout ty⌝ ∗
                  ⌜v `has_layout_val` ty_layout ty⌝ ∗ l ↦ v ∗ v ◁ᵥ ty.
Proof.
  iIntros "Hl".
  iDestruct (ty_aligned with "Hl") as %?.
  iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]".
  iDestruct (ty_size_eq with "Hv") as %?.
  iExists v. eauto with iFrame.
Qed.

Section proofs.
  Context `{!typeG Σ} `{!globalG Σ} `{!lockG Σ} `{!spinlockG Σ}.

  Typeclasses Transparent hyp_spinlock_t spinlock_token.

  (* Typing proof for [hyp_spin_lock_init]. *)
  Lemma type_hyp_spin_lock_init :
    ⊢ typed_function impl_hyp_spin_lock_init type_of_hyp_spin_lock_init.
  Proof.
    start_function "hyp_spin_lock_init" (p) => lock.
    split_blocks (∅ : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).
    (* Allocate the resources for the lock. *)
    iMod (alloc_lock_token_and_tickets) as (id) "(?&?&?)".
    (* Run the automation. *)
    repeat liRStep; liShow. rewrite right_id.
    (* Establish the invariant *)
    liInst Hevar id. iExists 0, 0.
    iFrame. iSplit; [ done | by iApply ticket_range_empty ].
    Unshelve. all: solve_goal.
  Qed.

  (* Typing proof for [hyp_spin_lock]. *)
  Lemma type_hyp_spin_lock :
    ⊢ typed_function impl_hyp_spin_lock type_of_hyp_spin_lock.
  Proof.
    start_function "hyp_spin_lock" ([[p id] s]) => var_lock local_got_it local_ticket local_next.
    split_blocks
      ((<[ "#1" :=
             (* First loop: checking that we got the ticket, we do if [got_it] is [true]. *)
             ∃ b : bool, ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ b @ boolean bool_it ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ∗
             (if b then ticket id i else True) ]> $
        <[ "#7" :=
             (* Nested loop: we read a potential ticket number.
                We will know that it is not NO_TICKET when we exit the loop. *)
             ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ uninit bool_it ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ]> $
        <[ "#4" :=
             (* Last loop: we have the ticket, waiting for our turn. *)
             ∃ i : Z,
             var_lock ◁ₗ p @ &frac{s} (hyp_spinlock_t id) ∗
             local_got_it ◁ₗ uninit bool_it ∗
             local_ticket ◁ₗ i @ int u16 ∗
             local_next ◁ₗ uninit u16 ∗
             ticket id i ]> ∅)%I : gmap label (iProp Σ))
      (∅ : gmap label (iProp Σ)).
    - (* #0 Initial block, running the nested loop for the first time. *)
      destruct s.
      + repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "([%%]&?&?&?&?&?&?)".
        repeat liRStep; liShow.
        liInst Hevar next.
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
        liInst Hevar owner. liInst Hevar0 next.
        repeat liRStep; liShow.
      + repeat liRStep; liShow.
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_read_end; iIntros "?".
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner next) "(%&Howner&Hnext&Hrest)".
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        iDestruct (ty_aligned with "Hnext") as %?.
        iDestruct (ty_deref with "Hnext") as (v) "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iExists 1%Qp, v, _, (t2mt (next @ int u16))%I.
        repeat liRStep; liShow. iSplit; first by iNext. iIntros "!> Hl".
        iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Howner Hrest Hl Hv]") as "_".
        { iNext. rewrite /hyp_spinlock_t_invariant. iExists owner, next.
          iFrame "Hrest". iSplit; first done. iFrame.
          by iApply (ty_ref with "[] Hl Hv"). }
        iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
        repeat liRStep; liShow.
    - (* #1 First loop (after the initial run), checking if we got the ticket. *)
      destruct s.
      + repeat liRStep; liShow. iIntros "Hb".
        repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "([%%]&?&?&?&?&?&?)".
        repeat liRStep; liShow.
        liInst Hevar next.
        rewrite /hyp_spinlock_t_invariant.
        repeat liRStep; liShow.
        liInst Hevar owner. liInst Hevar0 next.
        repeat liRStep; liShow.
        destruct b => //. iFrame.
      + repeat liRStep; liShow. iIntros "Hb".
        repeat liRStep; liShow.
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_read_end; iIntros "?".
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner next) "(%&Howner&Hnext&Hrest)".
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        iDestruct (ty_aligned with "Hnext") as %?.
        iDestruct (ty_deref with "Hnext") as (v') "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iExists 1%Qp, v', _, (t2mt (next @ int u16))%I.
        repeat liRStep; liShow. iSplit; first by iNext. iIntros "!> Hl".
        iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Howner Hrest Hl Hv]") as "_".
        { iNext. rewrite /hyp_spinlock_t_invariant. iExists owner, next.
          iFrame "Hrest". iSplit; first done. iFrame.
          by iApply (ty_ref with "[] Hl Hv"). }
        iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
        repeat liRStep; liShow.
        destruct b => //. iFrame.
    - (* #7 Code that eventually goes to the CAS and takes care of the loop. *)
      destruct s.
      + liRStepUntil typed_if. do 2 liRStep; liShow.
        * repeat liRStep; liShow.
          iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "([%%]&?&?&?&?&?&?)".
          repeat liRStep; liShow.
          liInst Hevar next.
          rewrite /hyp_spinlock_t_invariant.
          repeat liRStep; liShow.
          liInst Hevar owner. liInst Hevar0 next.
          repeat liRStep; liShow.
        * liRStepUntil typed_cas.
          iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "([%%]&?&?&?&?&?&?)".
          iIntros "???" (Φ) "HΦ".
          destruct (decide (next = i)) as [<-|] .
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (next + 1) @ int u16)%I into "Hnext+1".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_suc_int with "Hnext Hticket [$]"). { cbv. lia. } done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (t2mt (true @ boolean bool_it))%I) => //.
             repeat liRStep; liShow.
             rewrite /hyp_spinlock_t_invariant.
             repeat liRStep; liShow.
             liInst Hevar true.
             liInst Hevar1 owner.
             liInst Hevar2 (next + 1).
             liInst Hevar0 next.
             repeat liRStep; liShow.
             iRename select (ticket_range _ _ _) into "Htks".
             iDestruct (split_first_ticket with "Htks") as "[Hnext $]".
             { split; last by lia. by transitivity (min_int u16) => //. }
             iRename select (_ ∨ _)%I into "Hcases".
             iSplitL "Hcases".
             { iDestruct "Hcases" as "[[H %]|H]"; [iLeft | iRight] => //. iSplitL => //. iPureIntro. lia. }
             repeat liRStep; liShow.
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (i + 1) @ int u16)%I into "Hi+1".
             iDestruct select (_ ◁ᵥ (i + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_fail_int with "Hnext Hticket [$]"). { cbv. lia. } done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (t2mt (false @ boolean bool_it))%I) => //.
             repeat liRStep; liShow.
             rewrite /hyp_spinlock_t_invariant.
             repeat liRStep; liShow.
             liInst Hevar false.
             liInst Hevar1 owner.
             liInst Hevar2 next.
             liInst Hevar0 next.
             repeat liRStep; liShow.
      + liRStepUntil typed_if. do 2 liRStep; liShow.
        * repeat liRStep; liShow.
          iExists (Shr, place _); iSplitR; first by simpl.
          rewrite /typed_read_end; iIntros "?".
          iDestruct select (inv _ _) as "#Hinv".
          iInv "Hinv" as ">Inv" "Hclose_inv".
          iDestruct "Inv" as (owner next) "(%&Howner&Hnext&Hrest)".
          iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
          iDestruct (ty_aligned with "Hnext") as %?.
          iDestruct (ty_deref with "Hnext") as (v') "[Hl Hv]".
          iDestruct (ty_size_eq with "Hv") as %?.
          iExists 1%Qp, v', _, (t2mt (next @ int u16))%I.
          repeat liRStep; liShow. iSplit; first by iNext. iIntros "!> Hl".
          iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Howner Hrest Hl Hv]") as "_".
          { iNext. rewrite /hyp_spinlock_t_invariant. iExists owner, next.
            iFrame "Hrest". iSplit; first done. iFrame.
            by iApply (ty_ref with "[] Hl Hv"). }
          iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
          repeat liRStep; liShow.
        * liRStepUntil typed_cas.
          iIntros "???" (Φ) "HΦ".
          iDestruct select (inv _ _) as "#Hinv".
          iInv "Hinv" as ">Inv" "Hclose_inv".
          iDestruct "Inv" as (owner next) "([%%]&Howner&Hnext&Hrest)".
          destruct (decide (next = i)) as [<-|] .
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (next + 1) @ int u16)%I into "Hnext+1".
             iDestruct select (_ ◁ᵥ (next + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_suc_int with "Hnext Hticket [$]"). { cbv. lia. } done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (t2mt (true @ boolean bool_it))%I) => //.
             iRename select (p at{struct_hyp_spinlock}ₗ "next" ◁ₗ _)%I into "Hnext".
             iDestruct "Hrest" as "(Hfrag&Hr1&Hr2&Hcases)".
             iDestruct (split_first_ticket with "Hr2") as "[Hticket Hr2]".
             { split; last by lia. by transitivity (min_int u16). }
             iMod ("Hclose_inv" with "[Howner Hnext Hfrag Hr1 Hr2 Hcases]") as "_".
             { iNext. iExists owner, (next + 1). iFrame.
               iSplit. { iPureIntro. lia. }
               iDestruct "Hcases" as "[[H %]|H]"; [iLeft | iRight] => //.
               iSplitL => //. iPureIntro. lia. }
             iModIntro.
             repeat liRStep; liShow.
          ** iRename select (_ ◁ₗ next @ int u16)%I into "Hnext".
             iRename select (_ ◁ₗ (i + 1) @ int u16)%I into "Hi+1".
             iDestruct select (_ ◁ᵥ (i + 1) @ int u16)%I as "Hv".
             iDestruct select (local_ticket ◁ᵥ _)%I as "[_ Hticket]".
             iDestruct select (p at{_}ₗ _ ◁ᵥ _)%I as "[_ ->]".
             iApply (wp_cas_fail_int with "Hnext Hticket [$]"). { cbv. lia. } done.
             iNext. iIntros "??". iApply ("HΦ" $! _ (t2mt (false @ boolean bool_it))%I) => //.
             iRename select (p at{struct_hyp_spinlock}ₗ _ ◁ₗ _)%I into "Hnext".
             iMod ("Hclose_inv" with "[Howner Hnext Hrest]") as "_".
             { iNext. iExists owner, next. iFrame "Howner". iFrame "Hnext". iFrame "Hrest". done. }
             iModIntro.
             repeat liRStep; liShow.
    - (* #4 Final loop: checking if we are the owner. *)
      destruct s.
      + repeat liRStep; liShow.
        iDestruct select (hyp_spinlock_t_invariant _ _ _) as (owner next) "([%%]&?&?&?&?&?&?)".
        liRStepUntil typed_if. do 2 liRStep; liShow.
        * repeat liRStep; liShow. rewrite /hyp_spinlock_t_invariant. repeat liRStep; liShow.
          liInst Hevar0 owner. liInst Hevar1 next.
          repeat liRStep; liShow.
        * repeat liRStep; liShow. rewrite /hyp_spinlock_t_invariant. repeat liRStep; liShow.
          liInst Hevar i. liInst Hevar0 next.
          do 2 liRStep; liShow.
          iDestruct select (_ ∨ _)%I as "[[Ht _]|Htok]".
          { iExFalso. iRevert "Ht". iRename select (ticket _ _) into "Ht"; iRevert "Ht".
            iIntros "Ht1 Ht2". by iApply (ticket_non_duplicable with "Ht1 Ht2"). }
          iAssert (⌜i ≠ next⌝)%I as "%".
          { iIntros (<-). iRename select (ticket _ _) into "Hticket".
            iRename select (ticket_range _ i _) into "Hrange".
            iDestruct (ticket_not_NO_TICKET with "Hticket") as %Hi.
            iApply (ticket_already_in_range with "[] Hrange Hticket").
            iPureIntro. apply elem_of_seqZ. lia. }
          repeat liRStep; liShow.
          iSplitR "Htok"; last by iFrame. iLeft. iSplit => //. iPureIntro. lia.
      + repeat liRStep; liShow.
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_read_end; iIntros "?".
        iDestruct select (inv _ _) as "#Hinv".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner next) "([%%]&Howner&Hnext&Hrest)".
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        iDestruct (ty_aligned with "Howner") as %?.
        iDestruct (ty_deref with "Howner") as (w) "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iExists 1%Qp, w, _, (t2mt (owner @ int u16))%I.
        repeat liRStep; liShow. iSplit; first by iNext. iIntros "!> Hl".
        destruct (decide (i ≠ owner)).
        * iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Hnext Hrest Hl Hv]") as "_".
          { iNext. iExists owner, next. iFrame "Hrest". iSplit; first done. iFrame.
            by iApply (ty_ref with "[] Hl Hv"). }
          iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
          repeat liRStep; liShow.
        * assert (i = owner) as -> by lia.
          iRename select (ticket _ _) into "Hticket".
          iDestruct "Hrest" as "(Hfrag&Hr1&Hr2&Hcases)".
          iDestruct "Hcases" as "[[Hticket' %] | Htok]".
          { iExFalso. by iApply (ticket_non_duplicable with "Hticket Hticket'"). }
          iAssert (⌜owner ∈ u16⌝)%I as %[??].
          { rewrite /ty_own_val /=. by iDestruct "Hv" as %Hv%val_to_Z_in_range. }
          iAssert (⌜owner < next⌝)%I as %?.
          { destruct (decide (owner < next)); first done. iExFalso.
            iDestruct (ty_size_eq with "Hv") as %?.
            iDestruct (ticket_not_NO_TICKET with "Hticket") as %Howner.
            iApply (ticket_already_in_range with "[] Hr2 Hticket").
            iPureIntro. clear Q. apply elem_of_seqZ. lia. }
          iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Hnext Hl Hv Hfrag Hr1 Hr2 Hticket]") as "_".
          { iNext. iExists owner, next. iFrame "Hnext". iFrame "Hfrag". iSplit; first done.
            iDestruct (ty_ref with "[] Hl Hv") as "$" => //. iFrame "Hr1". iFrame "Hr2".
            iLeft. iSplit; done. }
          iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
          repeat liRStep; liShow.
    (* Solving side-conditions. *)
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try (repeat match goal with [ H : _ |- _ ] => revert H end;
      rewrite /LAST_TICKET /min_int /max_int /int_modulus /int_half_modulus;
      rewrite /bits_per_int /bytes_per_int /bits_per_byte /=; lia).
  Qed.

  (* Typing proof for [hyp_spin_unlock]. *)
  Lemma type_hyp_spin_unlock :
    ⊢ typed_function impl_hyp_spin_unlock type_of_hyp_spin_unlock.
  Proof.
    start_function "hyp_spin_unlock" ([[p id] s]) => lock ticket.
    split_blocks (∅ : gmap label (iProp Σ)) (∅ : gmap label (iProp Σ)).
    (* Extract the real token and our ticket number (owner) with a witness. *)
    iDestruct select (spinlock_token _ _) as (owner) "[Htok H●]".
    (* Run the automation, until we must look into the invariant. *)
    repeat liRStep; liShow. iIntros "Hinv". repeat liRStep; liShow.
    (* We do a different proof depending on the ownership state. *)
    destruct s.
    - (* [Own] case: we have full ownership. *)
      iDestruct select (hyp_spinlock_t_invariant _ _ _) as
          (owner' next) "([%%]&Howner&?&H◯&Hr1&?&Hcases)".
      (* We have the token: we are the owner and our ticket is in [Hcases]. *)
      iDestruct (owner_auth_agree with "H● H◯") as %<-.
      iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
      { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
        iApply (lock_token_exclusive with "Htok Htok'"). }
      (* We put our ticket at the end of the first ticket range. *)
      iDestruct (ty_own_int_in_range with "Howner") as %[Hmin ?].
      rewrite /min_int /= in Hmin.
      iDestruct (ticket_range_insert_r with "Hr1 Hticket") as "Hr1"; first by lia.
      (* Run the automation up to the [if] statement. *)
      liRStepUntil typed_if. liRStep; liRStep; liShow.
      + (* We have the last ticket. The next owner will be 0, we update. *)
        iMod (owner_auth_update _ _ _ _ 0%nat with "H● H◯") as "[??]".
        (* Run the automation to the end of the function. *)
        repeat (liRStep; liShow). rewrite right_id.
        (* Establish the invariant again, placing the token back inside. *)
        rewrite /hyp_spinlock_t_invariant. iExists 0, 0. iFrame.
        iSplit; first done. iSplitR; first by iApply ticket_range_empty.
        iRight. iFrame "Htok". by iExists _.
      + (* We do not have the last ticket, we do not reset the queue. *)
        iMod (owner_auth_update _ _ _ _ (owner + 1) with "H● H◯") as "[??]".
        (* Run the automation to the end of the function. *)
        repeat liRStep; liShow. rewrite right_id.
        (* Establish the invariant again, placing the token back inside. *)
        rewrite /hyp_spinlock_t_invariant. iExists (owner + 1), next. iFrame.
         iSplit. { iPureIntro. lia. } iRight. iFrame "Htok". by iExists _.
    - (* [Shr] case: we have shared ownership, we first run the automation. *)
      repeat liRStep; liShow.
      (* We must open the invariant to read. *)
      iExists (Shr, place _); iSplitR; first by simpl.
      rewrite /typed_read_end; iIntros "?".
      iDestruct select (inv _ _) as "#Hinv". iInv "Hinv" as ">Inv" "Hclose_inv".
      iDestruct "Inv" as (owner' next) "(%&Howner&Hnext&H◯&Hrest)".
      iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
      (* We have the token: we are the owner. *)
      iDestruct (owner_auth_agree with "H● H◯") as %<-.
      (* We perform the read. *)
      iDestruct (ty_aligned with "Howner") as %?.
      iDestruct (ty_deref with "Howner") as (v) "[Hl Hv]".
      iDestruct (ty_size_eq with "Hv") as %?.
      iExists 1%Qp, v, _, (t2mt (owner @ int u16))%I.
      repeat liRStep; liShow. iSplit; first by iNext. iIntros "!> Hl".
      (* We must close the invariant. *)
      iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Hnext Hrest Hl Hv H◯]") as "_".
      { iNext. rewrite /hyp_spinlock_t_invariant. iExists owner, next.
        iFrame "Hrest". iFrame. iSplit; first done.
        by iApply (ty_ref with "[] Hl Hv"). }
      iModIntro. iFrame select (_ ◁ₗ{Shr} _)%I.
      (* Run the automation to the write to [owner] of each branch. *)
      repeat liRStep; liShow.
      + (* We have the last ticket. The next owner will be 0, we update. *)
        (* We must open the invariant again. *)
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_write_end; iIntros "??".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner' next') "([%%]&Howner&Hnext&H◯&Htk1&Htk2&Hcases)".
        (* We have the token: we are the owner and our ticket is in [Hcases]. *)
        iDestruct (owner_auth_agree with "H● H◯") as %<-.
        iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
        { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
          iApply (lock_token_exclusive with "Htok Htok'"). }
        (* The owner will be 0, update the witness. *)
        iMod (owner_auth_update _ _ _ _ 0%nat with "H● H◯") as "[H● H◯]".
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        (* Learn that [next'] actually is [max_int u16]. *)
        iAssert ⌜next' = max_int u16⌝%I as %->.
        { iDestruct (ty_deref with "Hnext") as (w) "[_ H]". iDestruct "H" as %Hnext.
          iPureIntro. apply val_to_Z_in_range in Hnext as [??]. lia. }
        (* We perform the write and close the invariant. *)
        iDestruct (ty_aligned with "Howner") as %?.
        iDestruct (ty_deref with "Howner") as (v') "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iSplitL "Hl". { iExists _. by iFrame "Hl". }
        iIntros "!> Hl".
        iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Htok H● H◯ Hnext Hl Hv]") as "_".
        { iNext. iExists 0, (LAST_TICKET + 1). iFrame.
          iDestruct ((ty_ref (t := 0 @ int u16)) with "[] Hl []") as "$" => //.
          iSplit. { iPureIntro. split => //. }
          do 2 (iSplitR; first by iApply ticket_range_empty).
          iRight. iFrame "Htok". by iExists _. }
        iModIntro.
        (* We have all the tickets, let's combine them. *)
        iAssert (ticket_range id 0 (LAST_TICKET + 1)) with "[Htk1 Htk2 Hticket]" as "Htk".
        { iDestruct (ticket_range_insert_r with "Htk1 Hticket") as "Hr" => //. }
        (* Run the automation up to the write to the [next] field, open invariant. *)
        repeat liRStep; liShow.
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_write_end; iIntros "? ?".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner' next'') "([%%]&Howner&Hnext&H◯&Htr1&Htr2&Hcases)".
        (* We can get [owner' = 0] since we have all the tickets. *)
        iAssert ⌜owner' = 0⌝%I as %->.
        { destruct (decide (owner' = 0)) => //. iExFalso.
          iDestruct (ty_deref with "Howner") as (?) "[? Hv]".
          iDestruct "Hv" as %Howner%val_to_Z_in_range. destruct Howner as [Howner ?].
          iDestruct (overlaping_ticket_ranges with "[] Htk Htr1") as "$".
          iPureIntro. exists 0. split; apply elem_of_seqZ; try done.
          split => //. rewrite /min_int /= in Howner. lia. }
        (* Our ticket cannot be in [Hcases], we have it already. *)
        iDestruct "Hcases" as "[[?_] | Htok]".
        { iExFalso. iRename select (spinlock_def.ticket _ _) into "Hticket".
          iDestruct (ticket_already_in_range with "[] Htk Hticket") as "$".
          iPureIntro. apply elem_of_seqZ => //. }
        (* Learn that [next''] is [max_int u16]. *)
        iAssert ⌜next'' = max_int u16⌝%I as %->.
        { destruct (decide (next'' = max_int u16)); first done. iExFalso .
          destruct H as [??]. iDestruct (ty_own_int_in_range with "Hnext") as %[??].
          iDestruct (overlaping_ticket_ranges with "[] Htk Htr2") as "$".
          iExists next''. iPureIntro. split; apply elem_of_seqZ; lia. }
        (* We perform the write and close the invariant. *)
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        iDestruct (ty_aligned with "Hnext") as %?.
        iDestruct (ty_deref with "Hnext") as (v'') "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iSplitL "Hl". { iExists _. by iFrame "Hl". }
        iIntros "!> Hl".
        iRename select (ticket ◁ₗ _)%I into "Hticket_var".
        iMod "Hclose" as "_". iMod ("Hclose_inv" with "[- Hticket_var]") as "_".
        { iNext. iExists 0, 0. iFrame. iSplit; first by iPureIntro.
          iApply ((ty_ref (t := 0 @ int u16)) with "[] Hl []") => //. }
        iModIntro. iExists (place (p at{struct_hyp_spinlock}ₗ "next")).
        (* Run the automation to finish the branch. *)
        repeat liRStep; liShow.
      + (* We do not have the last ticket, we do not reset the queue. *)
        (* We must open the invariant again. *)
        iExists (Shr, place _); iSplitR; first by simpl.
        rewrite /typed_read_end; iIntros "? ?".
        iInv "Hinv" as ">Inv" "Hclose_inv".
        iDestruct "Inv" as (owner' next') "([% %]&Howner&Hnext&H◯&Htk1&Htk2&Hcases)".
        (* We have the token: we are the owner and our ticket is in [Hcases]. *)
        iDestruct (owner_auth_agree with "H● H◯") as %<-.
        iDestruct "Hcases" as "[[Hticket %] | Htok']"; last first.
        { iExFalso. iDestruct "Htok'" as (?) "[Htok' _]".
          iApply (lock_token_exclusive with "Htok Htok'"). }
        (* The owner will be [owner + 1], update the witness. *)
        iMod (owner_auth_update _ _ _ _ (owner + 1) with "H● H◯") as "[H● H◯]".
        iApply fupd_mask_intro; first solve_ndisj. iIntros "Hclose".
        (* We perform the write and close the invariant. *)
        iDestruct (ty_aligned with "Howner") as %?.
        iDestruct (ty_deref with "Howner") as (v') "[Hl Hv]".
        iDestruct (ty_size_eq with "Hv") as %?.
        iDestruct "Hv" as %?%val_to_Z_in_range.
        iSplitL "Hl". { iExists _. by iFrame "Hl". }
        iIntros "!> Hl".
        iMod "Hclose" as "_". iMod ("Hclose_inv" with "[Htok H● H◯ Hticket Hnext Hl Htk1 Htk2]") as "_".
        { iNext. iExists (owner + 1), next'. iFrame "Hnext". iFrame "H◯". iFrame "Htk2".
          iDestruct (ticket_range_insert_r with "Htk1 Hticket") as "$".
          { split; first done. by transitivity (min_int u16). }
          iSplit. { iPureIntro. by lia. }
          iDestruct ((ty_ref (t := (owner + 1) @ int u16)) with "[] Hl []") as "$" => //.
          { iPureIntro. rewrite /i2v.
            destruct (val_of_Z (owner + 1)) eqn:Heq => /=; first by apply val_to_of_Z.
            exfalso. assert (owner + 1 ∈ u16) as Hu16%val_of_Z_is_Some by (split; lia).
            destruct Hu16 as [??]. by simplify_eq. }
          iRight. iFrame "Htok". by iExists _. }
        iModIntro.
        (* Run the automation to finish the branch. *)
        repeat liRStep; liShow.
    (* Solving side-conditions. *)
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try (repeat match goal with [ H : _ |- _ ] => revert H end;
      rewrite /LAST_TICKET /min_int /max_int /int_modulus /int_half_modulus;
      rewrite /bits_per_int /bytes_per_int /bits_per_byte /=; lia).
  Qed.
End proofs.
