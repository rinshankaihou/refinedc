From iris.program_logic Require Export weakestpre.
From iris.base_logic.lib Require Export gen_heap.
From iris.proofmode Require Import tactics.
From iris.program_logic Require Import ectx_lifting.
From lithium.tutorial Require Export lang notation.
From lithium.tutorial Require Import tactics.

Class tutorialGS (Σ : gFunctors) := TutorialGS {
    tutorial_invGS : invGS Σ;
    tutorial_gen_heapGS :: gen_heapGS loc val Σ;
}.

Global Instance tutorial_irisG `{!tutorialGS Σ} : irisGS tutorial_lang Σ := {
  iris_invGS := tutorial_invGS;
  state_interp σ κs _ _ := gen_heap_interp σ.(heap);
  fork_post _ := True%I;
  num_laters_per_step _ := 0%nat;
  state_interp_mono _ _ _ _ := fupd_intro _ _;
}.

Notation "l ↦ dq v" := (mapsto l dq v)
  (at level 20, dq custom dfrac at level 1, format "l  ↦ dq  v") : bi_scope.


Section lifting.
  Context `{!tutorialGS Σ}.

  (** Heap *)
  Lemma wp_alloc s E Φ :
    (∀ l, l ↦ #0 -∗ Φ (LitV (LitLoc l))) -∗ WP Alloc @ s; E {{ Φ }}.
  Proof.
    iIntros "HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>"; iSplit; first by auto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep) "_Hcred"; inv_head_step.
    iMod (gen_heap_alloc with "Hσ") as "[Hσ [Hl _]]"; first done.
    iModIntro; iSplit=> //. iFrame. by iApply "HΦ".
  Qed.

  Lemma wp_load s E Φ (l : loc) v :
    l ↦ v -∗ Φ v -∗ WP Load #l @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep) "_Hcred"; inv_head_step.
    iModIntro; iSplit=> //. iFrame.
  Qed.

  Lemma wp_store s E Φ (l : loc) v (w : val) :
    l ↦ v -∗ Φ w -∗ WP Store #l w @ s; E {{ Φ }}.
  Proof.
    iIntros "Hl HΦ". iApply wp_lift_atomic_head_step_no_fork; first done.
    iIntros (σ1 κ κs n nt) "Hσ !>".
    iDestruct (gen_heap_valid with "Hσ Hl") as %?.
    iSplit; first by eauto with head_step.
    iIntros "!>" (v2 σ2 efs Hstep) "_Hcred"; inv_head_step.
    iMod (gen_heap_update with "Hσ Hl") as "[Hσ Hl]".
    iModIntro; iSplit=> //. iFrame.
  Qed.
End lifting.
