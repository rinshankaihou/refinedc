From iris.program_logic Require Export weakestpre.
From iris.proofmode Require Import coq_tactics reduction.
From iris.proofmode Require Export tactics.
From refinedc.lang Require Export tactics lifting.
From iris.program_logic Require Import lifting.
Set Default Proof Using "Type".
Import uPred.

Lemma tac_wps_bind `{refinedcG Σ} e Ks Q Ψ E s:
  W.find_stmt_fill s = Some (Ks, e) →
  WP (W.to_expr e) @ E {{ v, WPs W.to_stmt (W.stmt_fill Ks (W.Val v)) @ E {{ Q, Ψ }} }} -∗
  WPs (W.to_stmt s) @ E {{ Q, Ψ }}.
Proof.
  move => /W.find_stmt_fill_correct ->. iIntros "He".
  have [Ks' HKs']:= W.stmt_fill_correct Ks. rewrite HKs'.
  iApply wps_bind.
  iApply (wp_wand with "He"). iIntros (v).
  rewrite HKs' /W.to_expr. by iIntros "?".
Qed.

Tactic Notation "wps_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (stmt_wp ?E ?Q ?Ψ ?s) =>
    let s' := W.of_stmt s in change (stmt_wp E Q Ψ s) with (stmt_wp E Q Ψ (W.to_stmt s'));
    iApply tac_wps_bind; [done |];
    unfold W.to_expr, W.to_stmt; simpl; unfold W.to_expr; simpl
  | _ => fail "wps_bind: not a 'wp'"
  end.

Lemma tac_wp_bind' `{refinedcG Σ} e Ks Φ E:
  WP (W.to_expr e) @ E {{ v, WP (W.to_expr (W.fill Ks (W.Val v))) @ E{{ Φ }} }} -∗
  WP (W.to_expr (W.fill Ks e)) @ E {{ Φ }}.
Proof.
  move: Ks Φ => /=. elim/rev_ind. {
    iIntros (Φ) "He". iApply @wp_fupd.
    iApply (wp_wand with "He") => /=. iIntros (v). iApply @wp_value_inv'.
  }
  move => K Ks IH Φ.
  have [Ks' HKs']:= W.ectx_item_correct [K].
  rewrite W.fill_app HKs'.
  iIntros "He". iApply @wp_bind.
  iApply IH. iApply (wp_wand with "He").
  iIntros (v) "He".
  rewrite W.fill_app HKs'.
  by iApply @wp_bind_inv.
Qed.

Lemma tac_wp_bind `{refinedcG Σ} e Ks e' Φ E:
  W.find_expr_fill e false = Some (Ks, e') →
  WP (W.to_expr e') @ E {{ v, if Ks is [] then Φ v else WP (W.to_expr (W.fill Ks (W.Val v))) @ E{{ Φ }} }} -∗
  WP (W.to_expr e) @ E {{ Φ }}.
Proof.
  move => /W.find_expr_fill_correct ->. move: Ks => [|K Ks] //.
  move: (K::Ks) => {K}Ks. by iApply tac_wp_bind'.
Qed.

Tactic Notation "wp_bind" :=
  iStartProof;
  lazymatch goal with
  | |- envs_entails _ (wp ?s ?E ?e ?Φ) =>
    let e' := W.of_expr e in change (wp s E e Φ) with (wp s E (W.to_expr e') Φ);
    iApply tac_wp_bind; [done |];
    unfold W.to_expr; simpl
  | _ => fail "wp_bind: not a 'wp'"
  end.
