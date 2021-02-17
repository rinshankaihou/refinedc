From iris.proofmode Require Import tactics.
From iris.program_logic Require Export weakestpre.
From iris.program_logic Require Import ectx_lifting.
From refinedc.lang Require Export lang heap notation.
From refinedc.lang Require Import tactics.
Set Default Proof Using "Type".
Import uPred.

Class refinedcG Σ := RefinedCG {
  refinedcG_invG : invG Σ;
  refinedcG_gen_heapG :> heapG Σ
}.

Instance c_irisG `{!refinedcG Σ} : irisG c_lang Σ := {
  iris_invG := refinedcG_invG;
  state_interp σ κs _ := state_ctx σ;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

Instance into_val_val v : IntoVal (to_rtexpr (Val v)) v.
Proof. done. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Unfold heap_at : core.


Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; unfold coerce_rtexpr in *; simplify_eq; inv_expr_step; naive_solver
    |unfold coerce_rtexpr in *;apply ectxi_language_sub_redexes_are_values; intros [[]|[]] **; naive_solver].

Instance cas_atomic s ot (v1 v2 v3 : val) : Atomic s (coerce_rtexpr (CAS ot v1 v2 v3)).
Proof. solve_atomic. Qed.
Instance skipe_atomic s (v : val) : Atomic s (coerce_rtexpr (SkipE v)).
Proof. solve_atomic. Qed.
Instance deref_atomic s (l : loc) ly : Atomic s (coerce_rtexpr (Deref ScOrd ly l)).
Proof. solve_atomic. Qed.
Instance use_atomic s (l : loc) ly : Atomic s (coerce_rtexpr (Use ScOrd ly l)).
Proof. solve_atomic. Qed.

(*** General lifting lemmas *)

Section lifting.
  Context `{!refinedcG Σ}.
  Lemma wp_alloc_failed E Φ:
    ⊢ WP AllocFailed @ E {{ Φ }}.
  Proof.
    iLöb as "IH".
    iApply wp_lift_pure_det_head_step_no_fork' => //; first by eauto using AllocFailedStep.
    move => ????? . inversion 1; simplify_eq => //.
    match goal with | H: to_rtexpr ?e = AllocFailed |- _ => destruct e; discriminate end.
  Qed.

  Lemma wp_c_lift_step_fupd E e step_rel Φ:
    ((∃ e', e = to_rtexpr e' ∧ step_rel = expr_step e') ∨
     (∃ rf s, e = to_rtstmt rf s ∧ step_rel = stmt_step s rf)) →
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, step_rel σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜step_rel σ1 os e2 σ2 tsl⌝
          ={∅}=∗ ▷ (|={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }})))
      -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (He ?) "HWP".
    iApply wp_lift_head_step_fupd => //.
    iIntros (σ1 κ κs n) "Hσ".
    iMod ("HWP" $! σ1 with "Hσ") as (Hstep) "HWP".
    iModIntro. iSplit. {
      iPureIntro. destruct Hstep as (?&?&?&?&?).
      naive_solver eauto using ExprStep, StmtStep.
    }
    clear Hstep. iIntros (??? Hstep).
    destruct He as [[e' [??]]|[? [s [??]]]]; inversion Hstep; simplify_eq.
    all: try by [destruct e'; discriminate].
    all: try match goal with | H : to_rtexpr ?e = to_rtstmt _ _ |- _ => destruct e; discriminate end.
    all: iMod ("HWP" with "[//]") as "HWP".
    all: do 2 iModIntro.
    all: iMod "HWP" as (->) "[$ HWP]"; iModIntro => /=; by rewrite right_id.
  Qed.

  Lemma wp_lift_expr_step_fupd E (e : expr) Φ:
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜expr_step e σ1 os e2 σ2 tsl⌝
          ={∅}=∗ ▷ (|={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }})))
      -∗ WP e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply wp_c_lift_step_fupd => //. naive_solver. Qed.

  Lemma wp_lift_stmt_step_fupd E s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s rf σ1 os e2 σ2 tsl⌝ ∗
        (∀ os e2 σ2 tsl, ⌜stmt_step s rf σ1 os e2 σ2 tsl⌝
          ={∅}=∗ ▷ (|={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }})))
      -∗ WP to_rtstmt rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply wp_c_lift_step_fupd => //. naive_solver. Qed.

  Lemma wp_c_lift_step E e step_rel Φ:
    ((∃ e', e = to_rtexpr e' ∧ step_rel = expr_step e') ∨
     (∃ rf s, e = to_rtstmt rf s ∧ step_rel = stmt_step s rf)) →
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, step_rel σ1 os e2 σ2 tsl⌝ ∗
        ▷ (∀ os e2 σ2 tsl, ⌜step_rel σ1 os e2 σ2 tsl⌝
          ={E}=∗ ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP e @ E {{ Φ }}.
  Proof.
    iIntros (??) "HWP".
    iApply wp_c_lift_step_fupd => //.
    iIntros (?) "Hσ". iMod ("HWP" with "Hσ") as "[$ HWP]".
    iApply fupd_mask_intro; first set_solver. iIntros "HE".
    iIntros (?????) "!> !>". iMod "HE". by iMod ("HWP" with "[//]") as "$".
  Qed.

  Lemma wp_lift_expr_step E (e : expr) Φ:
    to_val e = None →
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, expr_step e σ1 os e2 σ2 tsl⌝ ∗
        ▷ (∀ os e2 σ2 tsl, ⌜expr_step e σ1 os e2 σ2 tsl⌝
          ={E}=∗ ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP e @ E {{ Φ }}.
  Proof. iIntros (?) "HWP". iApply wp_c_lift_step => //. naive_solver. Qed.

  Lemma wp_lift_stmt_step E s rf Φ:
    (∀ (σ1 : state), state_ctx σ1 ={E}=∗
       ⌜∃ os e2 σ2 tsl, stmt_step s rf σ1 os e2 σ2 tsl⌝ ∗
        ▷ (∀ os e2 σ2 tsl, ⌜stmt_step s rf σ1 os e2 σ2 tsl⌝
          ={E}=∗ ⌜tsl = []⌝ ∗ state_ctx σ2 ∗ WP e2 @ E {{ Φ }}))
      -∗ WP to_rtstmt rf s @ E {{ Φ }}.
  Proof. iIntros "HWP". iApply wp_c_lift_step => //. naive_solver. Qed.

End lifting.

(*** Lifting of expressions *)
Section expr_lifting.
Context `{!refinedcG Σ}.

Lemma wp_binop v1 v2 Φ op E ot1 ot2:
  (∀ σ, state_ctx σ -∗
    ⌜∃ v', eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ ∗
    ▷ (∀ v', ⌜eval_bin_op op ot1 ot2 σ v1 v2 v'⌝ -∗ state_ctx σ ∗ Φ v')) -∗
  WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "Hctx !>".
  iDestruct ("HΦ" with "Hctx") as ([v' Heval]) "HΦ".
  iSplit; first by eauto 8 using BinOpS.
  iIntros "!#" (? e2 σ2 efs Hst). inv_expr_step.
  iDestruct ("HΦ" with "[//]") as "[$ HΦ]".
  iModIntro. iSplit => //. by iApply wp_value.
Qed.

Lemma wp_binop_det v' v1 v2 Φ op E ot1 ot2:
  (∀ σ v, state_ctx σ -∗ ⌜eval_bin_op op ot1 ot2 σ v1 v2 v ↔ v = v'⌝) ∧ ▷ Φ v' -∗
    WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_binop. iIntros (σ) "Hctx". iSplit.
  { iExists v'. iDestruct "H" as "[Hσ _]". by iDestruct ("Hσ" with "Hctx") as %->. }
  iIntros "!>" (v Hbinop). iAssert (⌜v = v'⌝)%I as %->.
  { iDestruct "H" as "[Hσ _]". iDestruct ("Hσ" with "Hctx") as %Hvv'.
    iPureIntro. naive_solver. }
  by iDestruct "H" as "[_ $]".
Qed.

Lemma wp_unop v1 Φ op E ot:
  (∀ σ, state_ctx σ -∗
    ⌜∃ v', eval_un_op op ot σ v1 v'⌝ ∗
    ▷ (∀ v', ⌜eval_un_op op ot σ v1 v'⌝ -∗ state_ctx σ ∗ Φ v')) -∗
   WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "Hctx !>".
  iDestruct ("HΦ" with "Hctx") as ([v' Heval]) "HΦ".
  iSplit; first by eauto 8 using UnOpS.
  iIntros "!#" (? e2 σ2 efs Hst). inv_expr_step.
  iDestruct ("HΦ" with "[//]") as "[$ HΦ]".
  iModIntro. iSplit => //. by iApply wp_value.
Qed.

Lemma wp_unop_det v' v1 Φ op E ot:
  (∀ σ v, state_ctx σ -∗ ⌜eval_un_op op ot σ v1 v ↔ v = v'⌝) ∧ ▷ Φ v' -∗
  WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros "H".
  iApply wp_unop. iIntros (σ) "Hctx". iSplit.
  { iExists v'. iDestruct "H" as "[Hσ _]". by iDestruct ("Hσ" with "Hctx") as %->. }
  iIntros "!>" (v Hbinop). iAssert (⌜v = v'⌝)%I as %->.
  { iDestruct "H" as "[Hσ _]". iDestruct ("Hσ" with "Hctx") as %Hvv'.
    iPureIntro. naive_solver. }
  by iDestruct "H" as "[_ $]".
Qed.

Lemma wp_deref v Φ vl l ly q E o:
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  l `has_layout_loc` ly →
  v `has_layout_val` ly →
  l↦{q}v -∗ ▷ (l ↦{q} v -∗ Φ v) -∗ WP !{ly, o} (Val vl) @ E {{ Φ }}.
Proof.
  iIntros (Ho Hl Hll Hlv) "Hmt HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros ([h ub fn]) "(%&Hhctx&Hactx&Hfctx)/=".
  iDestruct (heap_mapsto_has_alloc_id with "Hmt") as %Haid.
  destruct o; try by destruct Ho.
  - iModIntro. iDestruct (heap_mapsto_lookup_q (λ st, ∃ n, st = RSt n) with "Hhctx Hmt") as %Hat. naive_solver.
    iSplit; first by eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst) "!> !>". inv_expr_step.
    iSplit => //. unfold end_st, end_expr.
    have <- : (v = v') by apply: heap_at_inj_val.
    rewrite /heap_fmap/=. erewrite heap_upd_heap_at_id => //.
    iFrame. iApply wp_value. by iApply "HΦ".
  - iMod (heap_read_na with "Hhctx Hmt") as "(% & Hσ & Hσclose)" => //. iModIntro.
    iSplit; first by eauto 11 using DerefS.
    iIntros (? e2 σ2 efs Hst) "!> !>". inv_expr_step.
    iSplit => //. unfold end_st, end_expr.
    have <- : (v = v') by apply: heap_at_inj_val.
    iFrame => /=.

    iApply wp_lift_expr_step; auto.
    iIntros ([h2 ub2 fn2]) "(%&Hhctx&Hactx&Hfctx)/=".
    iMod ("Hσclose" with "Hhctx") as (?) "(Hσ & Hv)".
    iModIntro; iSplit; first by eauto 11 using DerefS.
    iIntros "!#" (? e2 σ2 efs Hst) "!#". inv_expr_step. iSplit => //.
    have ? : (v = v'0) by apply: heap_at_inj_val. subst.
    iFrame. iApply wp_value. by iApply "HΦ".
Qed.

(*
  Alternative version of the CAS rule which does not rely on the Atomic infrastructure:
  Lemma wp_cas vl1 vl2 vd Φ l1 l2 it E:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  (bytes_per_int it ≤ bytes_per_addr)%nat →
  (|={E, ∅}=> ∃ (q1 q2 : Qp) vo ve z1 z2,
     ⌜val_to_int vo it = Some z1⌝ ∗ ⌜val_to_int ve it = Some z2⌝ ∗
     ⌜l1 `has_layout_loc` it_layout it⌝ ∗ ⌜l2 `has_layout_loc` it_layout it⌝ ∗
     ⌜length vd = bytes_per_int it⌝ ∗ ⌜if bool_decide (z1 = z2) then q1 = 1%Qp else q2 = 1%Qp⌝ ∗
     l1↦{q1}vo ∗ l2↦{q2}ve ∗ ▷ (
       l1↦{q1} (if bool_decide (z1 = z2) then vd else vo) -∗
       l2↦{q2} (if bool_decide (z1 = z2) then ve else vo)
       ={∅, E}=∗ Φ (val_of_bool (bool_decide (z1 = z2))))) -∗
   WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
*)

Lemma wp_cas_fail vl1 vl2 vd vo ve z1 z2 Φ l1 l2 it q E:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` it_layout it →
  l2 `has_layout_loc` it_layout it →
  val_to_int vo it = Some z1 →
  val_to_int ve it = Some z2 →
  length vd = bytes_per_int it →
  (bytes_per_int it ≤ bytes_per_addr)%nat →
  z1 ≠ z2 →
  l1↦{q}vo -∗ l2↦ve -∗ ▷ (l1 ↦{q} vo -∗ l2↦vo -∗ Φ (val_of_bool false)) -∗
   WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_has_alloc_id with "Hl1") as %Haid1.
  iDestruct (heap_mapsto_has_alloc_id with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl1") as %? => //. { naive_solver. }
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl2") as %? => //.
  iModIntro. iSplit; first by eauto 15 using CasFailS.
  iIntros (? e2 σ2 efs Hst) "!>". inv_expr_step;
    have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence];
    have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length ve0 = length vo0) by congruence.
  iMod (heap_write with "Hhctx Hl2") as "[$ Hl2]" => //. iModIntro.
  iFrame. iSplit => //. iApply wp_value. by iApply ("HΦ" with "[$]").
Qed.

Lemma wp_cas_suc vl1 vl2 vd vo ve z1 z2 Φ l1 l2 it E q:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` it_layout it →
  l2 `has_layout_loc` it_layout it →
  val_to_int vo it = Some z1 →
  val_to_int ve it = Some z2 →
  length vd = bytes_per_int it →
  (bytes_per_int it ≤ bytes_per_addr)%nat →
  z1 = z2 →
  l1↦vo -∗ l2↦{q}ve -∗ ▷ (l1 ↦ vd -∗ l2↦{q}ve -∗ Φ (val_of_bool true)) -∗
  WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_has_alloc_id with "Hl1") as %Haid1.
  iDestruct (heap_mapsto_has_alloc_id with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl1") as %? => //.
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl2") as %? => //. { naive_solver. }
  iModIntro. iSplit; first by eauto 15 using CasSucS.
  iIntros (? e2 σ2 efs Hst) "!>". inv_expr_step;
      have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence];
      have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length vo0 = length vd) by congruence.
  iMod (heap_write with "Hhctx Hl1") as "[$ Hmt]" => //. iModIntro.
  iFrame. iSplit => //. iApply wp_value. by iApply ("HΦ" with "[$]").
Qed.

Lemma wp_neg_int Φ v v' n E it:
  val_to_int v it = Some n →
  val_of_int (-n) it = Some v' →
  ▷ Φ (v') -∗ WP UnOp NegOp (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply wp_unop_det. iSplit => //.
  iIntros (σ v2) "_ !%". split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_int Φ v v' n E its itt:
  val_to_int v its = Some n →
  val_of_int n itt = Some v' →
  ▷ Φ (v') -∗ WP UnOp (CastOp (IntOp itt)) (IntOp its) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply wp_unop_det. iSplit => //.
  iIntros (σ v2) "_ !%". split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_loc Φ v l E:
  val_to_loc v = Some l →
  ▷ Φ (val_of_loc l) -∗ WP UnOp (CastOp PtrOp) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det. iSplit => //.
  iIntros (σ v2) "_ !%". split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_ptr_int Φ v v' l E it:
  val_to_loc v = Some l →
  val_of_int l.2 it = Some v' →
  ▷ Φ (v') -∗ WP UnOp (CastOp (IntOp it)) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply wp_unop_det. iSplit => //.
  iIntros (σ ?) "_ !%". split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_cast_int_ptr Φ v n E it:
  val_to_int v it = Some n →
  ▷ Φ (val_of_loc (None, n)) -∗ WP UnOp (CastOp PtrOp) (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop_det. iSplit => //.
  iIntros (σ ?) "_ !%". split.
  - by inversion 1; simplify_eq.
  - move => ->. by econstructor.
Qed.

Lemma wp_copy_alloc_id Φ l1 l2 v1 v2 E:
  val_to_loc v1 = Some l1 →
  val_to_loc v2 = Some l2 →
  ▷ Φ (val_of_loc (l2.1, l1.2)) -∗ WP CopyAllocId (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2) "HΦ". iApply wp_lift_expr_step => //.
  iIntros (σ1) "Hctx !>". iSplit; first by eauto 8 using CopyAllocIdS.
  iIntros "!>" (???? Hstep) "!>". inv_expr_step. iSplit => //. iFrame.
  by iApply wp_value.
Qed.

Lemma wp_ptr_relop Φ op v1 v2 l1 l2 E b:
  val_to_loc v1 = Some l1 →
  val_to_loc v2 = Some l2 →
  match op with
  | EqOp => Some (bool_decide (l1.2 = l2.2))
  | NeOp => Some (bool_decide (l1.2 ≠ l2.2))
  | LtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 < l2.2)) else None
  | GtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 > l2.2)) else None
  | LeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 <= l2.2)) else None
  | GeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 >= l2.2)) else None
  | _ => None
  end = Some b →
  loc_in_bounds l1 0 -∗ loc_in_bounds l2 0 -∗
  (alloc_alive l1 ∧ alloc_alive l2 ∧ ▷ Φ (i2v (Z_of_bool b) i32)) -∗
  WP BinOp op PtrOp PtrOp (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hv1 Hv2 Hop) "#Hl1 #Hl2 HΦ".
  iApply wp_binop. iIntros (σ) "Hσ".
  iAssert ⌜valid_ptr l1 σ⌝%I as %?. {
    iApply (alloc_alive_to_valid_ptr with "Hl1 [HΦ] Hσ").
    by iDestruct "HΦ" as "[$ _]".
  }
  iAssert ⌜valid_ptr l2 σ⌝%I as %?. {
    iApply (alloc_alive_to_valid_ptr with "Hl2 [HΦ] Hσ").
    by iDestruct "HΦ" as "[_ [$ _]]".
  }
  iSplit; first by iPureIntro; eexists _; econstructor.
  iDestruct "HΦ" as "(_&_&HΦ)". iIntros "!>" (v' Hstep). iFrame.
  inversion Hstep; simplify_eq => //; by move: Hv1 Hv2 => /val_of_to_loc ?/val_of_to_loc?; subst.
Qed.

Lemma wp_ptr_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_int vo it = Some o →
  0 ≤ o →
  ▷ Φ (val_of_loc (l offset{ly}ₗ o)) -∗ WP Val vl at_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo Ho) "HΦ".
  iApply wp_binop_det. iSplit; last done.
  iIntros (σ v) "_ !%". split.
  - inversion 1. by simplify_eq.
  - move => ->. by apply PtrOffsetOpIP.
Qed.

Lemma wp_ptr_neg_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_int vo it = Some o →
  ▷ Φ (val_of_loc (l offset{ly}ₗ -o)) -∗ WP Val vl at_neg_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo) "HΦ".
  iApply wp_binop_det. iSplit; last done.
  iIntros (σ v) "_ !%". split.
  - inversion 1. by simplify_eq.
  - move => ->. by apply PtrNegOffsetOpIP.
Qed.

Lemma wp_get_member Φ vl l sl n E:
  val_to_loc vl = Some l →
  is_Some (index_of sl.(sl_members) n) →
  ▷ Φ (val_of_loc (l at{sl}ₗ n)) -∗ WP Val vl at{sl} n @ E {{ Φ }}.
Proof.
  iIntros (Hvl [i Hi]) "HΦ".
  rewrite /GetMember/GetMemberLoc/offset_of Hi /=.
  have [|? Hs]:= (val_of_int_is_some size_t (offset_of_idx sl.(sl_members) i)). {
    split; first by rewrite /min_int/=; lia.
    by apply offset_of_bound.
  }
  rewrite Hs /=. move: Hs => /val_to_of_int Hs.
  iApply wp_binop_det. iSplit; last done.
  iIntros (σ v) "_ !%". split.
  - inversion 1; simplify_eq. by rewrite offset_loc_sz1.
  - move => ->. rewrite -(offset_loc_sz1 u8) //. apply: PtrOffsetOpIP => //. lia.
Qed.

Lemma wp_get_member_union Φ vl l ul n E:
  val_to_loc vl = Some l →
  Φ (val_of_loc (l at_union{ul}ₗ n)) -∗ WP Val vl at_union{ul} n @ E {{ Φ }}.
Proof. iIntros (->%val_of_to_loc) "?". rewrite /GetMemberUnion/GetMemberUnionLoc. by iApply @wp_value. Qed.

Lemma wp_offset_of Φ s m i E:
  offset_of s.(sl_members) m = Some i →
  (∀ v, ⌜val_of_int i size_t = Some v⌝ -∗ Φ v) -∗
  WP OffsetOf s m @ E {{ Φ }}.
Proof.
  rewrite /OffsetOf. iIntros (Ho) "HΦ".
  have [|? Hs]:= (val_of_int_is_some size_t i). {
    split; first by rewrite /min_int/=; lia.
    move: Ho => /fmap_Some[?[?->]].
    by apply offset_of_bound.
  }
  rewrite Ho /= Hs /=. iApply wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_offset_of_union Φ ul m E:
  Φ (i2v 0 size_t) -∗ WP OffsetOfUnion ul m @ E {{ Φ }}.
Proof. by iApply @wp_value. Qed.

Lemma wp_if Φ it v e1 e2 n:
  val_to_int v it = Some n →
  (if decide (n = 0) then WP coerce_rtexpr e2 {{ Φ }} else WP coerce_rtexpr e1 {{ Φ }}) -∗
  WP IfE (IntOp it) (Val v) e1 e2 {{ Φ }}.
Proof.
  iIntros (?) "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro. iSplit; first by eauto 8 using IfES.
  iIntros (? ? σ2 efs Hst) "!> !>". inv_expr_step.
  iSplit => //. iFrame.
  by case_decide; case_bool_decide.
Qed.

Lemma wp_skip Φ v E:
  ▷ Φ v -∗ WP SkipE (Val v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?". iModIntro. iSplit; first by eauto 8 using SkipES.
  iIntros (? e2 σ2 efs Hst) "!> !>". inv_expr_step.
  iSplit => //. iFrame. by iApply wp_value.
Qed.

Lemma wp_concat E Φ vs:
  Φ (mjoin vs) -∗ WP Concat (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_expr_step; auto.
  iIntros (σ1) "?".
  iModIntro. iSplit; first by eauto 8 using ConcatS.
  iIntros "!#" (? e2 σ2 efs Hst). inv_expr_step.
  iModIntro. iSplit => //. iFrame. by iApply wp_value.
Qed.

Lemma wps_concat_bind_ind vs E Φ es:
  foldr (λ e f, (λ vl, WP coerce_rtexpr e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Concat (Val <$> (vs ++ vl)) @ E {{ Φ }}) es [] -∗
  WP Concat ((Val <$> vs) ++ es) @ E {{ Φ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: es vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    have -> : (coerce_rtexpr (Concat ((Val <$> vs ++ vl2) ++ e :: el)))%E = (fill [ExprCtx (ConcatCtx (vs ++ vl2) (to_rtexpr <$> el))] (to_rtexpr e)). {
        by rewrite /coerce_rtexpr/= fmap_app fmap_cons -!list_fmap_compose.
    }
    iApply wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Expr (RTConcat ((Expr <$> (RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr <$> el)))
             = Concat ((Val <$> vs ++ (vl2 ++ [v])) ++ el). 2: by iApply IH.
    by rewrite /coerce_rtexpr /= !fmap_app /= (cons_middle (of_val v)) !app_assoc -!list_fmap_compose.
Qed.

Lemma wp_concat_bind E Φ es:
  foldr (λ e f, (λ vl, WP coerce_rtexpr e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Concat (Val <$> vl) @ E {{ Φ }}) es [] -∗
  WP Concat es @ E {{ Φ }}.
Proof. by iApply (wps_concat_bind_ind []). Qed.

Lemma wp_struct_init E Φ sl fs:
  foldr (λ '(n, ly) f, (λ vl,
     WP coerce_rtexpr (default (Val (replicate (ly_size ly) MPoison)) (n' ← n; (list_to_map fs : gmap _ _) !! n'))
        @ E {{ v, f (vl ++ [v]) }}))
    (λ vl, Φ (mjoin vl)) sl.(sl_members) [] -∗
  WP StructInit sl fs @ E {{ Φ }}.
Proof.
  iIntros "He". unfold StructInit. iApply wp_concat_bind.
  move: {2 4}[] => vs.
  iInduction (sl_members sl) as [|[o?]?] "IH" forall (vs) => /=. by iApply wp_concat.
  iApply (wp_wand with "He"). iIntros (v') "Hfold". by iApply "IH".
Qed.

Lemma wp_call_bind_ind vs E Φ vf el:
  foldr (λ e f, (λ vl, WP coerce_rtexpr e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP (Call (Val vf) (Val <$> (vs ++ vl))) @ E {{ Φ }}) el [] -∗
  WP (Call (Val vf) ((Val <$> vs) ++ el)) @ E {{ Φ}}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: el vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    have -> : (coerce_rtexpr (Call (Val vf) ((Val <$> vs ++ vl2) ++ e :: el)))%E = (fill [ExprCtx (CallRCtx vf (vs ++ vl2) (to_rtexpr <$> el))] (to_rtexpr e)). {
        by rewrite /coerce_rtexpr/= fmap_app fmap_cons -!list_fmap_compose.
    }
    iApply wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    have -> : Expr (RTCall vf ((Expr <$> (RTVal <$> vs ++ vl2)) ++ of_val v :: (to_rtexpr <$> el)))
             = Call vf ((Val <$> vs ++ (vl2 ++ [v])) ++ el). 2: by iApply IH.
    by rewrite /coerce_rtexpr /= !fmap_app /= (cons_middle (of_val v)) !app_assoc -!list_fmap_compose.
Qed.

Lemma wp_call_bind E Φ el ef:
  WP (coerce_rtexpr ef) @ E {{ vf, foldr (λ e f, (λ vl, WP coerce_rtexpr e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP (Call (Val vf) (Val <$> vl)) @ E {{ Φ }}) el [] }} -∗
  WP (Call ef el) @ E {{ Φ }}.
Proof.
  iIntros "HWP".
  have -> : coerce_rtexpr (Call ef el) = fill [ExprCtx $ CallLCtx (coerce_rtexpr <$> el)] (coerce_rtexpr ef) by [].
  iApply wp_bind.
  iApply (wp_wand with "HWP"). iIntros (vf) "HWP".
  by iApply (wp_call_bind_ind []).
Qed.

End expr_lifting.

(*** Lifting of statements *)
Definition stmt_wp_def `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) (s : stmt) : iProp Σ :=
  (∀ Φ rf, ⌜Q = rf.(rf_fn).(f_code)⌝ -∗ (∀ v, Ψ v -∗ WP to_rtstmt rf (Return v) {{ Φ }}) -∗
    WP to_rtstmt rf s @ E {{ Φ }}).
Definition stmt_wp_aux `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) : seal (@stmt_wp_def Σ _ E Q Ψ). by eexists. Qed.
Definition stmt_wp `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) :
  stmt → iProp Σ := (stmt_wp_aux E Q Ψ).(unseal).
Definition stmt_wp_eq `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) : stmt_wp E Q Ψ = @stmt_wp_def Σ _ E Q Ψ := (stmt_wp_aux E Q Ψ).(seal_eq).

Notation "'WPs' s @ E {{ Q , Ψ } }" := (stmt_wp E Q Ψ s%E)
  (at level 20, s, Q, Ψ at level 200, format "'[' 'WPs'  s  '/' '[       ' @  E  {{  Q ,  Ψ  } } ']' ']'" ) : bi_scope.

Notation "'WPs' s {{ Q , Ψ } }" := (stmt_wp ⊤ Q Ψ s%E)
  (at level 20, s, Q, Ψ at level 200, format "'[' 'WPs'  s  '/' '[   ' {{  Q ,  Ψ  } } ']' ']'") : bi_scope.

Section stmt_lifting.
Context `{!refinedcG Σ}.

Lemma stmt_wp_unfold s E Q Ψ  :
  WPs s @ E {{ Q, Ψ }} ⊣⊢ stmt_wp_def E Q Ψ s.
Proof. by rewrite stmt_wp_eq. Qed.

Lemma fupd_wps s E Q Ψ :
  (|={E}=> WPs s @ E {{ Q, Ψ }}) -∗ WPs s @ E{{ Q, Ψ }}.
Proof.
  rewrite stmt_wp_unfold. iIntros "Hs" (? rf HQ) "HΨ".
  iApply fupd_wp. by iApply "Hs".
Qed.

Global Instance elim_modal_bupd_wps p s Q Ψ P E :
    ElimModal True p false (|==> P) P (WPs s @ E {{ Q, Ψ }}) (WPs s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim (bupd_fupd E) fupd_frame_r wand_elim_r fupd_wps. Qed.

Global Instance elim_modal_fupd_wps p s Q Ψ P E :
    ElimModal True p false (|={E}=> P) P (WPs s @ E {{ Q, Ψ }}) (WPs s @ E {{ Q, Ψ }}).
Proof. by rewrite /ElimModal intuitionistically_if_elim fupd_frame_r wand_elim_r fupd_wps. Qed.

Lemma wps_wand s E Q Φ Ψ:
  WPs s @ E {{ Q , Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPs s @ E {{ Q , Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "HΦ H" (???) "HΨ".
  iApply "HΦ"; [ done | ..]. iIntros (v) "Hv".
  iApply "HΨ". iApply "H". iApply "Hv".
Qed.

Lemma wp_call vf vl f fn Φ:
  val_to_loc vf = Some f →
  Forall2 has_layout_val vl (f_args fn).*2 →
  fntbl_entry f fn -∗ ▷(∀ lsa lsv, ⌜Forall2 has_layout_loc lsa (f_args fn).*2⌝ -∗
     ([∗ list] l; v ∈ lsa; vl, l↦v) -∗ ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) -∗ ∃ Ψ',
          WPs Goto fn.(f_init) {{ (subst_stmt (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> (lsa ++ lsv)))) <$> fn.(f_code), Ψ' }} ∗
         (∀ v, Ψ' v -∗
                  ([∗ list] l; v ∈ lsa; fn.(f_args), l↦|v.2|) ∗
                  ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) ∗
                  Φ v)
   ) -∗
   WP (Call (Val vf) (Val <$> vl)) {{ Φ }}.
Proof.
  move => Hf Hly. move: (Hly) => /Forall2_length. rewrite fmap_length => Hlen_vs.
  iIntros "Hf HWP". iApply wp_lift_expr_step; auto.
  iIntros (σ1) "(%&Hhctx&Hbctx&Hfctx)".
  iDestruct (fntbl_entry_lookup with "Hfctx Hf") as %Hfn. iModIntro.
  iSplit; first by eauto 10 using CallFailS.
  iIntros (???? Hstep) "!>". inv_expr_step; last first. {
    (* Alloc failure case. *)
    iModIntro. iSplit; first done. rewrite /state_ctx. iFrame. iApply wp_alloc_failed.
  }
  iMod (heap_alloc_new_blocks_upd with "[$Hhctx $Hbctx $Hfctx]") as "[Hctx Hlv]" => //.
  iMod (heap_alloc_new_blocks_upd with "Hctx") as "[Hctx Hla]" => //.
  iModIntro. iSplit => //.

  iDestruct ("HWP" $! lsa lsv with "[//] Hla [Hlv]") as (Ψ') "(HQinit & HΨ')". {
    rewrite big_sepL2_fmap_r. iApply (big_sepL2_mono with "Hlv") => ??? ?? /=.
    iIntros "?". iExists _. iFrame. iPureIntro. split; first by apply replicate_length.
    apply: Forall2_lookup_lr. 2: done. done. rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
  }
  iFrame. rewrite stmt_wp_eq. iApply "HQinit" => //.

  (** prove Return *)
  iIntros (v) "Hv". iDestruct ("HΨ'" with "Hv") as "(Ha & Hv & Hs)".
  iApply wp_lift_stmt_step => //.
  iIntros (σ3) "(%&Hhctx&Hrest) !>".
  iSplit; first by eauto 8 using ReturnS.
  iIntros (os ts3 σ2' ? Hst). inv_stmt_step. iIntros "!>". iSplitR => //.
  iFrame. rewrite /heap_fmap/= heap_free_list_app /=.
  rewrite -!(big_sepL2_fmap_r snd (λ _ l ly, l↦|ly|)%I).
  iMod (heap_free_list_free with "Hhctx Hv") as "Hhctx".
  iMod (heap_free_list_free with "Hhctx Ha") as "$".
  iModIntro. by iApply wp_value.
Qed.

Lemma wps_return Q Ψ v:
  Ψ v -∗ WPs (Return (Val v)) {{ Q , Ψ }}.
Proof. rewrite stmt_wp_unfold. iIntros "Hb" (? rf ?) "HΨ". by iApply "HΨ". Qed.

Lemma wps_goto Q Ψ b s:
  Q !! b = Some s →
  ▷ WPs s {{ Q, Ψ }} -∗ WPs Goto b {{ Q , Ψ }}.
Proof.
  iIntros (Hs) "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step. iIntros (?) "Hσ !>".
  iSplit; first by eauto 10 using GotoS.
  iIntros (???? Hstep) "!> !>". inv_stmt_step.
  iSplit; first done. iFrame. by iApply "HWP".
Qed.

Lemma wps_skip Q Ψ s:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs SkipS s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step_fupd. iIntros (?) "Hσ".
  iMod "HWP" as "HWP". iModIntro.
  iSplit; first by eauto 10 using SkipSS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext.
  iMod "HWP". iModIntro. iSplit; first done. iFrame.
  by iApply "HWP".
Qed.

Lemma wps_exprs Q Ψ s v:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs ExprS (Val v) s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". rewrite !stmt_wp_unfold. iIntros (???) "?". subst.
  iApply wp_lift_stmt_step_fupd. iIntros (?) "Hσ".
  iMod "HWP" as "HWP". iModIntro.
  iSplit; first by eauto 10 using ExprSS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext.
  iMod "HWP". iModIntro. iSplit; first done. iFrame.
  by iApply "HWP".
Qed.

Lemma wps_annot n A (a : A) Q Ψ s:
  (|={⊤}[∅]▷=>^n WPs s {{ Q, Ψ }}) -∗ WPs AnnotStmt n a s {{ Q , Ψ }}.
Proof.
  iIntros "Hs". iInduction n as [|n] "IH" => /=. by iApply "Hs".
  rewrite /AnnotStmt. iApply wps_skip. by iApply (step_fupd_wand with "Hs IH").
Qed.

Lemma wps_assign Q Ψ vl ly vr s l o:
  let E := if o is ScOrd then ∅ else ⊤ in
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  vr `has_layout_val` ly →
  (|={⊤,E}=> l↦|ly| ∗ ▷ (l↦vr ={E,⊤}=∗ WPs s {{Q, Ψ}}))
    -∗ WPs (Val vl <-{ly, o} Val vr; s) {{ Q , Ψ }}.
Proof.
  iIntros (E Ho Hvl Hly) "HWP". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step_fupd. iIntros ([h1 ?]) "(%&Hhctx&Hfctx)/=". iMod "HWP" as "[Hl HWP]".
  iApply (fupd_mask_weaken ∅); first set_solver. iIntros "HE".
  iDestruct "Hl" as (v' ? ?) "Hl".
  iDestruct (heap_mapsto_has_alloc_id with "Hl") as %Haid.
  unfold E. case: Ho => ->.
  - iModIntro.
    iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl") as %? => //.
    iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hstep) "!> !>". inv_stmt_step. unfold end_val.
    iMod (heap_write with "Hhctx Hl") as "[$ Hl]" => //. congruence.
    iMod ("HWP" with "Hl") as "HWP".
    iModIntro => /=. iSplit; first done. iFrame. by iApply "HWP".
  - iMod (heap_write_na _ _ _ vr with "Hhctx Hl") as (?) "[Hhctx Hc]" => //; first by congruence.
    iModIntro. iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hst) "!> !>". inv_stmt_step.
    have ? : (v' = v'0) by [apply: heap_at_inj_val]; subst v'0.
    iFrame => /=. iMod "HE" as "_". iModIntro. iSplit; first done.

    (* second step *)
    iApply wp_lift_stmt_step.
    iIntros ([h2 ?]) "(%&Hhctx&Hfctx)" => /=.
    iMod ("Hc" with "Hhctx") as (?) "[Hhctx Hmt]".
    iModIntro. iSplit; first by eauto 12 using AssignS. unfold end_stmt.
    iIntros (? e2 σ2 efs Hst) "!>". inv_stmt_step.
    have ? : (v' = v'0) by [apply: heap_at_go_inj_val']; subst v'0.
    iFrame => /=. iMod ("HWP" with "Hmt") as "HWP".
    iModIntro. iSplit; first done.
    by iApply "HWP".
Qed.

Lemma wps_switch Q Ψ v n ss def m it:
  val_to_int v it = Some n →
  (∀ i, m !! n = Some i → is_Some (ss !! i)) →
  WPs default def (i ← m !! n; ss !! i) {{ Q, Ψ }} -∗ WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hm) "HWP". rewrite !stmt_wp_eq. iIntros (?? ->) "?".
  iApply wp_lift_stmt_step. iIntros (?) "Hσ".
  iModIntro. iSplit; first by eauto 8 using SwitchS.
  iIntros (???? Hstep) "!> !>". inv_stmt_step. iSplit; first done.
  iFrame "Hσ". by iApply "HWP".
Qed.

(** a version of wps_switch which is directed by ss instead of n *)
Lemma wps_switch' Q Ψ v n ss def m it:
  val_to_int v it = Some n →
  map_Forall (λ _ i, is_Some (ss !! i)) m →
  ([∧ list] i↦s∈ss, ⌜m !! n = Some i⌝ -∗ WPs s {{ Q, Ψ }}) ∧
  (⌜m !! n = None⌝ -∗ WPs def {{ Q, Ψ }}) -∗
  WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  iIntros (Hn Hm) "Hs". iApply wps_switch; eauto.
  destruct (m !! n) as [i|] eqn:Hi => /=.
  - iDestruct "Hs" as "[Hs _]".
    destruct (ss !! i) as [s|] eqn:? => /=. 2: by move: (Hm _ _ Hi) => [??]; simplify_eq.
    by iApply (big_andL_lookup with "Hs").
  - iDestruct "Hs" as "[_ Hs]". by iApply "Hs".
Qed.

Lemma wps_if Q Ψ v s1 s2 n:
  val_to_int v bool_it = Some n →
  (if decide (n = 0) then WPs s2 {{ Q, Ψ }} else WPs s1 {{ Q, Ψ }}) -∗
  WPs (if: (Val v) then s1 else s2) {{ Q , Ψ }}.
Proof.
  iIntros (Hn) "Hs". iApply wps_switch' => //=.
  1: by apply map_Forall_insert_2; eauto; apply map_Forall_empty.
  rewrite right_id. by iSplit; iIntros (?); simplify_map_eq.
Qed.

Lemma wps_assert Q Ψ v s n:
  val_to_int v bool_it = Some n → n ≠ 0 →
  WPs s {{ Q, Ψ }} -∗
  WPs (assert: Val v; s) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hn) "Hs". rewrite /notation.Assert.
  iApply wps_if => //. by case_decide.
Qed.

Definition wps_block (P : iProp Σ) (b : label) (Q : gmap label stmt) (Ψ : val → iProp Σ) : iProp Σ :=
  (□ (P -∗ WPs Goto b {{ Q, Ψ }})).

Lemma wps_block_rec Ps Q Ψ :
  ([∗ map] b ↦ P ∈ Ps, ∃ s, ⌜Q !! b = Some s⌝ ∗ □(([∗ map] b ↦ P ∈ Ps, wps_block P b Q Ψ) -∗ P -∗ WPs s {{ Q, Ψ }})) -∗
  [∗ map] b ↦ P ∈ Ps, wps_block P b Q Ψ.
Proof.
  iIntros "#HQ". iLöb as "IH".
  iApply (big_sepM_impl with "HQ").
  iIntros "!#" (b P HPs).
  iDestruct 1 as (s HQ) "#Hs".
  iIntros "!# HP".
  iApply wps_goto. by apply: lookup_weaken.
  iModIntro. by iApply "Hs".
Qed.

End stmt_lifting.
