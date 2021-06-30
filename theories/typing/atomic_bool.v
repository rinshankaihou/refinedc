From refinedc.typing Require Export type.
From refinedc.typing Require Import programs int.
Set Default Proof Using "Type".

Definition atomic_boolN : namespace := nroot.@"atomic_boolN".
Section atomic_bool.
  Context `{!typeG Σ}.

  Program Definition atomic_bool (it : int_type) (PT PF : iProp Σ) : type := {|
    ty_own β l :=
      match β return _ with
      | Own => ∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF
      | Shr => ⌜l `has_layout_loc` it⌝ ∗
               inv atomic_boolN (∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF)
      end;
  |}%I.
  Next Obligation.
    iIntros "%it %PT %PF %l %E %HE (%b&Hb&Hown)".
    iDestruct (ty_aligned with "Hb") as %?. iSplitR => //.
    iApply inv_alloc. iNext. iExists b. iFrame.
  Qed.

  Global Program Instance movable_atomic_bool it PT PF : Movable (atomic_bool it PT PF) := {|
    ty_layout := it_layout it;
    ty_own_val v := ∃ b, v ◁ᵥ b @ boolean it ∗ if b then PT else PF;
  |}%I.
  Next Obligation. iIntros (????) "[% [Hb _]]". by iApply (ty_aligned with "Hb"). Qed.
  Next Obligation. iIntros (????) "[% [Hb _]]". by iApply (ty_size_eq with "Hb"). Qed.
  Next Obligation.
    iIntros (????) "[% [Hb ?]]".
    iDestruct (ty_deref with "Hb") as (?) "[? ?]".
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (??????) "Hl [%b [Hb ?]]".
    iDestruct (ty_ref with "[] Hl Hb") as "?" => //.
    iExists b. iFrame.
  Qed.

  Global Instance alloc_alive_atomic_bool it β PT PF:
    AllocAlive (atomic_bool it PT PF) β True.
  Proof.
    constructor. have ?:= bytes_per_int_gt_0 it. destruct β.
    - iIntros (l) "? (%b&Hl&?)". iApply (alloc_alive_alive with "[] Hl"). iPureIntro.
      rewrite /ly_size/=. lia.
    - iIntros (l) "? (%&Hl)".
      iApply (heap_mapsto_alive_strong).
      iInv "Hl" as "(%b&>Hb&?)" "Hclose".
      iApply fupd_mask_intro; [set_solver|]. iIntros "_".
      rewrite /ty_own/=.
      iDestruct "Hb" as "(%v&%&%&?)". iExists _, _. iFrame. iPureIntro.
      erewrite val_to_Z_length; [|done]. lia.
  Qed.

End atomic_bool.
Notation "atomic_bool< it , PT , PF >" := (atomic_bool it PT PF)
  (only printing, format "'atomic_bool<' it ,  PT ,  PF '>'") : printing_sugar.

Section programs.
  Context `{!typeG Σ}.

  Lemma subsume_atomic_bool_own_int l n it PT PF T:
    (∃ b, subsume (l ◁ₗ n @ int it) (l ◁ₗ b @ boolean it) ((if b then PT else PF) ∗ T)) -∗
    subsume (l ◁ₗ n @ int it) (l ◁ₗ atomic_bool it PT PF) T.
  Proof.
    iDestruct 1 as (b) "Hsub". iIntros "Hl".
    iDestruct ("Hsub" with "Hl") as "[? [? $]]".
    iExists _. by iFrame.
  Qed.
  Global Instance subsume_atomic_bool_own_int_inst l n it PT PF:
    Subsume (l ◁ₗ n @ int it)%I (l ◁ₗ atomic_bool it PT PF) :=
    λ T, i2p (subsume_atomic_bool_own_int l n it PT PF T).

  Lemma type_read_atomic_bool l β it PT PF T:
    (∀ b v,
      destruct_hint (DHintDestruct bool b) tt (
        (if b then PT else PF) -∗
        (if b then PT else PF) ∗
        T v (atomic_bool it PT PF) (t2mt (b @ boolean it))
      )
    ) -∗
    typed_read_end true l β (atomic_bool it PT PF) it T.
  Proof.
    unfold destruct_hint. iIntros "HT Hl". destruct β.
    - iDestruct "Hl" as "[%b [Hl Hif]]".
      iApply fupd_mask_intro => //. iIntros "Hclose".
      iDestruct (ty_aligned with "Hl") as %?.
      iDestruct (ty_deref with "Hl") as (v) "[Hl #Hv]".
      iDestruct (ty_size_eq with "Hv") as %?.
      iExists _, _, _, (t2mt (b @ boolean it)).
      iFrame "∗Hv". do 2 iSplitR => //=.
      iIntros "!# Hl". iMod "Hclose". iModIntro.
      iDestruct ("HT" with "Hif") as "[Hif $]".
      iExists b. iFrame. by iApply (ty_ref with "[] Hl Hv").
    - iDestruct "Hl" as (Hly) "#Hinv".
      iInv "Hinv" as (b) "[>Hl Hif]" "Hclose".
      iApply fupd_mask_intro. set_solver. iIntros "Hclose2".
      iDestruct (ty_aligned with "Hl") as %?.
      iDestruct (ty_deref with "Hl") as (?) "[Hmt #Hv]".
      iDestruct (ty_size_eq with "Hv") as %?.
      iExists _, _, _, (t2mt (b @ boolean it)). iFrame "Hmt Hv".
      iSplit; [done|]. iSplit; [done|].
      iIntros "!# Hl". iDestruct ("HT" with "Hif") as "[Hif $]".
      iMod "Hclose2" as "_".
      iMod ("Hclose" with "[-]"). { iExists b. iModIntro. iFrame. by iApply (ty_ref with "[] Hl Hv"). }
      iModIntro. by iSplitR.
  Qed.
  Global Instance type_read_atomic_bool_inst l β it PT PF:
    TypedReadEnd true l β (atomic_bool it PT PF) it | 10 :=
    λ T, i2p (type_read_atomic_bool l β it PT PF T).

  Lemma type_write_atomic_bool l β it PT PF v ty `{!Movable ty} T:
    (∃ b,
      subsume (v ◁ᵥ ty) (v ◁ᵥ b @ boolean it) (
        ⌜ty.(ty_layout) = it⌝ ∗
        (if b then PT else PF) ∗
        T (atomic_bool it PT PF)
      )
    ) -∗
    typed_write_end true v ty l β (atomic_bool it PT PF) T.
  Proof.
    iIntros "[%bnew Hsub] Hl Hv".
    iDestruct ("Hsub" with "Hv") as "(#Hnew&->&Hif_new&HT)".
    destruct β.
    - iDestruct "Hl" as "[%bold [Hl Hif_old]]".
      iApply fupd_mask_intro => //. iIntros "Hc".
      iDestruct (ty_aligned with "Hl") as %?.
      iDestruct (ty_deref with "Hl") as (vb) "[Hmt Hold]".
      iDestruct (ty_size_eq with "Hold") as %?.
      iSplitL "Hmt". by iExists _; iFrame.
      iIntros "!# Hl". iMod "Hc". iModIntro.
      iExists _. iFrame. iExists bnew. iFrame.
      iApply (@ty_ref with "[] Hl") => //. done.
    - iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as (b) "[>Hmt Hif]" "Hc".
      iApply fupd_mask_intro; first solve_ndisj.
      iIntros "Hc2".
      iDestruct (ty_aligned with "Hmt") as %?.
      iDestruct (ty_deref with "Hmt") as (?) "[Hmt #Hv]".
      iDestruct (ty_size_eq with "Hv") as %?.
      iSplitL "Hmt". { iExists _; by iFrame. }
      iIntros "!# Hl". iMod "Hc2".
      iMod ("Hc" with "[Hif_new Hl]").
      { iModIntro. iExists bnew. iFrame. by iApply (@ty_ref with "[] Hl Hnew"). }
      iModIntro. iExists _. iFrame. by iSplit.
  Qed.
  Global Instance type_write_atomic_bool_inst l β it PT PF v ty `{!Movable ty}:
    TypedWriteEnd true v ty l β (atomic_bool it PT PF) | 10 :=
    λ T, i2p (type_write_atomic_bool l β it PT PF v ty T).

  Lemma type_cas_atomic_bool (l : loc) β it PT PF lexp Pexp vnew Pnew T:
    (∃ bexp bnew,
      subsume Pexp (lexp ◁ₗ bexp @ boolean it) (
        subsume Pnew (vnew ◁ᵥ bnew @ boolean it) (
          ⌜bytes_per_int it ≤ bytes_per_addr⌝%nat ∗ (
            ((if bexp then PT else PF) -∗
             (if bnew then PT else PF) ∗ (
                l ◁ₗ{β} atomic_bool it PT PF -∗ lexp ◁ₗ bexp @ boolean it -∗
                T (val_of_bool true) (t2mt (true @ boolean bool_it)))) ∧
            (l ◁ₗ{β} atomic_bool it PT PF -∗
             lexp ◁ₗ negb bexp @ boolean it -∗
             T (val_of_bool false) (t2mt (false @ boolean bool_it)))
           )
        )
      )
    ) -∗
    typed_cas (IntOp it) l (l ◁ₗ{β} (atomic_bool it PT PF))%I lexp Pexp vnew Pnew T.
  Proof.
    iIntros "(%bexp&%bnew&Hsub) Hl Hlexp Hvnew".
    iDestruct ("Hsub" with "Hlexp") as "[Hlexp Hsub]".
    iDestruct ("Hsub" with "Hvnew") as "[#Hvnew [% Hsub]]".
    iIntros (Φ) "HΦ".
    destruct β.
    - iDestruct "Hl" as (b) "[Hb Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_bool with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iApply "HΦ". 2: iApply ("HT" with "[Hb Hif] Hexp"). done.
        iExists bnew. by iFrame.
      + iApply (wp_cas_fail_bool with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[_ HT]".
        iApply "HΦ". 2: iApply ("HT" with "[Hb Hif]"). done.
        * iExists b. iFrame.
        * by destruct b, bexp.
    - iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as "Hb".
      iDestruct "Hb" as (b) "[>Hmt Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_bool with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iModIntro. iSplitL "Hb Hif". { iExists bnew. iFrame. }
        iApply "HΦ". 2: iApply ("HT" with "[] Hexp"). done.
        by iSplit.
      + iApply (wp_cas_fail_bool with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[_ HT]".
        iModIntro. iSplitL "Hb Hif". { by iExists b; iFrame; rewrite /i2v Hvnew. }
        iApply "HΦ". 2: iApply ("HT" with "[]"). done.
        * by iSplit.
        * by destruct b, bexp.
  Qed.
  Global Instance type_cas_atomic_bool_inst (l : loc) β it PT PF (lexp : loc) Pexp vnew Pnew:
    TypedCas (IntOp it) l (l ◁ₗ{β} (atomic_bool it PT PF))%I lexp Pexp vnew Pnew :=
    λ T, i2p (type_cas_atomic_bool l β it PT PF lexp Pexp vnew Pnew T).

End programs.

Typeclasses Opaque atomic_bool.
