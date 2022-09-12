From refinedc.typing Require Export type.
From refinedc.typing Require Import programs boolean int.
Set Default Proof Using "Type".

Definition atomic_boolN : namespace := nroot.@"atomic_boolN".
Section atomic_bool.
  Context `{!typeG Σ}.

  Program Definition atomic_bool (it : int_type) (PT PF : iProp Σ) : type := {|
    ty_has_op_type ot mt := is_bool_ot ot it StrictBool;
    ty_own β l :=
      match β return _ with
      | Own => ∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF
      | Shr => ⌜l `has_layout_loc` it⌝ ∗
               inv atomic_boolN (∃ b, l ◁ₗ b @ boolean it ∗ if b then PT else PF)
      end;
    ty_own_val v := ∃ b, v ◁ᵥ b @ boolean it ∗ if b then PT else PF;
  |}%I.
  Next Obligation.
    iIntros "%it %PT %PF %l %E %HE (%b&Hb&Hown)".
    iDestruct (ty_aligned _ (IntOp _) MCNone with "Hb") as %?; [done|]. iSplitR => //.
    iApply inv_alloc. iNext. iExists b. iFrame.
  Qed.
  Next Obligation. iIntros (???????) "[% [Hb _]]". by iApply (ty_aligned with "Hb"). Qed.
  Next Obligation. iIntros (???????) "[% [Hb _]]". by iApply (ty_size_eq with "Hb"). Qed.
  Next Obligation.
    iIntros (???????) "[% [Hb ?]]".
    iDestruct (ty_deref with "Hb") as (?) "[? ?]"; [done|].
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (?????????) "Hl [%b [Hb ?]]".
    iDestruct (ty_ref with "[] Hl Hb") as "?" => //.
    iExists b. iFrame.
  Qed.
  Next Obligation.
    iIntros (it PT PF v ot mt st ?) "(%&Hv&?)".
    iDestruct (ty_memcast_compat with "Hv") as "Hv"; [done|]. destruct mt => //.
    iExists _. iFrame.
  Qed.

  Global Instance alloc_alive_atomic_bool it β PT PF:
    AllocAlive (atomic_bool it PT PF) β True.
  Proof.
    constructor. have ?:= bytes_per_int_gt_0 it. destruct β.
    - iIntros (l) "? (%b&Hl&?)". by iApply (alloc_alive_alive with "[] Hl").
    - iIntros (l) "? (%&Hl)".
      iApply (heap_mapsto_alive_strong).
      iInv "Hl" as "(%b&>Hb&?)" "Hclose".
      iApply fupd_mask_intro; [set_solver|]. iIntros "_".
      rewrite /ty_own/=.
      iDestruct "Hb" as "(%v&%n&%&%&%&?)". iExists _, _. iFrame. iPureIntro.
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

  Lemma subsume_atomic_bool_own_bool l (b : bool) it PT PF T:
    ((if b then PT else PF) ∗ T) -∗
    subsume (l ◁ₗ b @ boolean it) (l ◁ₗ atomic_bool it PT PF) T.
  Proof. iIntros "[? $] Hl". iExists _. by iFrame. Qed.
  Global Instance subsume_atomic_bool_own_bool_inst l b it PT PF:
    Subsume (l ◁ₗ b @ boolean it)%I (l ◁ₗ atomic_bool it PT PF) :=
    λ T, i2p (subsume_atomic_bool_own_bool l b it PT PF T).

  Lemma type_read_atomic_bool l β it ot PT PF mc T:
    (⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗
      ∀ b v,
      destruct_hint (DHintDestruct bool b) tt (
        (if b then PT else PF) -∗
        (if b then PT else PF) ∗
        T v (atomic_bool it PT PF) (b @ boolean it)
      )
    ) -∗
    typed_read_end true ⊤ l β (atomic_bool it PT PF) ot mc T.
  Proof.
    unfold destruct_hint. iIntros "[%Hot HT]".
    iApply typed_read_end_mono_strong; [done|]. destruct β.
    - iIntros "[%b [Hl Hif]] !>". iExists _, _, True%I. iFrame. iSplitR; [done|].
      unshelve iApply (type_read_copy with "[HT Hif]"). { apply _. } simpl.
      iSplit; [by destruct ot; simplify_eq/=|]. iSplit; [done|]. iIntros (v) "_ Hl Hv".
      iDestruct ("HT" with "Hif") as "[Hif HT]". iExists _, _. iFrame "HT Hv".
      iExists _. by iFrame.
    - iIntros "[%Hly #Hinv] !>".
      iExists Own, tytrue, True%I. iSplit; [done|]. iSplit; [done|].
      iInv "Hinv" as (b) "[>Hl Hif]".
      iApply typed_read_end_mono_strong; [done|]. iIntros "_ !>".
      iExists _, _, _. iFrame.
      unshelve iApply (type_read_copy with "[-]"). { apply _. } simpl.
      iSplit; [by destruct ot; simplify_eq/=|]. iSplit; [iPureIntro; solve_ndisj|].
      iIntros (v) "Hif Hl #Hv !>".
      iDestruct ("HT" with "Hif") as "[Hif HT]". iExists tytrue, tytrue.
      iSplit; [done|]. iSplit; [ done |]. iModIntro.
      iSplitL "Hl Hif". { iExists _. by iFrame. }
      iIntros "_ _ _ !>". iExists _, _. iFrame "∗Hv". by iSplit.
  Qed.
  Global Instance type_read_atomic_bool_inst l β it ot mc PT PF:
    TypedReadEnd true ⊤ l β (atomic_bool it PT PF) ot mc | 10 :=
    λ T, i2p (type_read_atomic_bool l β it ot PT PF mc T).

  Lemma type_write_atomic_bool l β it ot PT PF v ty T:
    (⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗ ∃ b,
      subsume (v ◁ᵥ ty) (v ◁ᵥ b @ boolean it) (
        (if b then PT else PF) ∗
        T (atomic_bool it PT PF)
      )
    ) -∗
    typed_write_end true ⊤ ot v ty l β (atomic_bool it PT PF) T.
  Proof.
    iIntros "[% [%bnew Hsub]]". iApply typed_write_end_mono_strong; [done|].
    iIntros "Hv Hl". iModIntro.
    iDestruct ("Hsub" with "Hv") as "(#Hnew&Hif_new&HT)".
    destruct β.
    - iDestruct "Hl" as "[%bold [Hl Hif_old]]".
      iExists (_ @ boolean it)%I, _, _, True%I. iFrame "∗". iSplitR; [done|]. iSplitR; [done|].
      iApply type_write_own_copy. { by destruct ot; simplify_eq/=. }
      iSplit; [by destruct ot; simplify_eq/=|].
      iIntros "Hv _ Hl !>". iExists _. iFrame "HT". iExists _. by iFrame.
    - iExists tytrue, Own, tytrue, True%I. iSplit; [done|]. iSplit; [done|]. iSplit; [done|].
      iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as (b) "[>Hmt Hif]".
      iApply typed_write_end_mono_strong; [done|]. iIntros "_ _". iModIntro.
      iExists _, _, _, True%I. iFrame. iSplitR; [done|]. iSplitR; [done|].
      iApply type_write_own_copy. { by destruct ot; simplify_eq/=. }
      iSplit; [by destruct ot; simplify_eq/=|].
      iIntros "Hv _ Hl !>". iExists tytrue. iSplit; [done|]. iModIntro.
      iSplitL "Hif_new Hl". { iExists _. by iFrame. }
      iIntros "_ _ !>". iExists _. iFrame "HT". by iSplit.
  Qed.
  Global Instance type_write_atomic_bool_inst l β it ot PT PF v ty:
    TypedWriteEnd true ⊤ ot v ty l β (atomic_bool it PT PF) | 10 :=
    λ T, i2p (type_write_atomic_bool l β it ot PT PF v ty T).

  Lemma type_cas_atomic_bool (l : loc) β ot it PT PF lexp Pexp vnew Pnew T:
    (⌜match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end⌝ ∗ ∃ bexp bnew,
      subsume Pexp (lexp ◁ₗ bexp @ boolean it) (
        subsume Pnew (vnew ◁ᵥ bnew @ boolean it) (
          ⌜ly_size (ot_layout ot) ≤ bytes_per_addr⌝%nat ∗ (
            ((if bexp then PT else PF) -∗
             (if bnew then PT else PF) ∗ (
                l ◁ₗ{β} atomic_bool it PT PF -∗ lexp ◁ₗ bexp @ boolean it -∗
                T (val_of_bool true) (true @ builtin_boolean))) ∧
            (l ◁ₗ{β} atomic_bool it PT PF -∗
             lexp ◁ₗ negb bexp @ boolean it -∗
             T (val_of_bool false) (false @ builtin_boolean))
           )
        )
      )
    ) -∗
    typed_cas ot l (l ◁ₗ{β} (atomic_bool it PT PF))%I lexp Pexp vnew Pnew T.
  Proof.
    iIntros "(%&%bexp&%bnew&Hsub) Hl Hlexp Hvnew".
    iDestruct ("Hsub" with "Hlexp") as "[Hlexp Hsub]".
    iDestruct ("Hsub" with "Hvnew") as "[#Hvnew [% Hsub]]".
    iIntros (Φ) "HΦ".
    destruct β.
    - iDestruct "Hl" as (b) "[Hb Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_boolean with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iApply "HΦ"; last first.
        * iApply ("HT" with "[Hb Hif] Hexp"). iExists bnew. by iFrame.
        * by iExists _.
      + iApply (wp_cas_fail_boolean with "Hb Hlexp") => //.
        iIntros "!# Hb Hexp". iDestruct "Hsub" as "[_ HT]".
        iApply "HΦ"; last first.
        * iApply ("HT" with "[Hb Hif]"). { iExists _. by iFrame. } by destruct b, bexp.
        * by iExists _.
    - iDestruct "Hl" as (?) "#Hinv".
      iInv "Hinv" as "Hb".
      iDestruct "Hb" as (b) "[>Hmt Hif]".
      destruct (decide (b = bexp)); subst.
      + iApply (wp_cas_suc_boolean with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[Hsub _]". iDestruct ("Hsub" with "Hif") as "[Hif HT]".
        iModIntro. iSplitL "Hb Hif". { iExists bnew. iFrame. }
        iApply "HΦ"; last first.
        * iApply ("HT" with "[] Hexp"). by iSplit.
        * by iExists _.
      + iApply (wp_cas_fail_boolean with "Hmt Hlexp") => //.
        iIntros "!# Hb Hexp".
        iDestruct "Hsub" as "[_ HT]".
        iModIntro. iSplitL "Hb Hif". { by iExists b; iFrame; rewrite /i2v Hvnew. }
        iApply "HΦ"; last first.
        * iApply ("HT" with "[]"); first by iSplit. by destruct b, bexp.
        * by iExists _.
  Qed.
  Global Instance type_cas_atomic_bool_inst (l : loc) β it ot PT PF (lexp : loc) Pexp vnew Pnew:
    TypedCas ot l (l ◁ₗ{β} (atomic_bool it PT PF))%I lexp Pexp vnew Pnew :=
    λ T, i2p (type_cas_atomic_bool l β ot it PT PF lexp Pexp vnew Pnew T).

End programs.

Global Typeclasses Opaque atomic_bool.
