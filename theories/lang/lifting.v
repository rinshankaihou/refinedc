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

Instance expr_irisG `{!refinedcG Σ} : irisG expr_lang Σ := {
  iris_invG := refinedcG_invG;
  state_interp σ κs _ := state_ctx σ;
  fork_post _ := True%I;
}.
Instance stmt_irisG `{!refinedcG Σ} : irisG stmt_lang Σ := {
  iris_invG := refinedcG_invG;
  state_interp σ κs _ := state_ctx σ;
  fork_post _ := True%I;
}.
Global Opaque iris_invG.

Instance into_val_val v : IntoVal (Val v) v.
Proof. done. Qed.

Local Hint Extern 0 (reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : core.
Local Hint Unfold heap_at : core.


Local Ltac solve_atomic :=
  apply strongly_atomic_atomic, ectx_language_atomic;
    [inversion 1; naive_solver
    |apply ectxi_language_sub_redexes_are_values; intros [] **; naive_solver].

Instance cas_atomic s ot (v1 v2 v3 : val) : Atomic s (CAS ot v1 v2 v3).
Proof. solve_atomic. Qed.
Instance skipe_atomic s (v : val) : Atomic s (SkipE v).
Proof. solve_atomic. Qed.

(*** Lifting of expressions *)

Section expr_lifting.
Context `{!refinedcG Σ}.

Lemma wp_binop v' v1 v2 Φ op E ot1 ot2:
  (∀ h, eval_bin_op op ot1 ot2 h v1 v2 v') →
  ▷ (∀ v h, ⌜eval_bin_op op ot1 ot2 h v1 v2 v⌝ -∗ Φ v) -∗
   WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ".
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "[Hhctx Hfctx]".
  iModIntro. iSplit; first by eauto using BinOpS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
  iFrame. iModIntro. iSplitL => //. by iApply "HΦ".
Qed.

Lemma wp_binop_det v' v1 v2 Φ op E ot1 ot2:
  (∀ h v, eval_bin_op op ot1 ot2 h v1 v2 v ↔ v = v') →
  ▷ Φ v' -∗ WP BinOp op ot1 ot2 (Val v1) (Val v2) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ".
  iApply (wp_binop v'). by move => h; apply Hop.
  iIntros "!#" (v h). rewrite Hop. iIntros (?). subst. by iApply "HΦ".
Qed.

Lemma wp_unop v' v1 Φ op E ot:
  (∀ h, eval_un_op op ot h v1 v') →
  ▷ (∀ v h, ⌜eval_un_op op ot h v1 v⌝ -∗ Φ v) -∗
   WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ".
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "[Hhctx Hfctx]".
  iModIntro. iSplit; first by eauto using UnOpS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
  iFrame. iModIntro. iSplitL => //. by iApply "HΦ".
Qed.

Lemma wp_unop_det v' v1 Φ op E ot:
  (∀ h v, eval_un_op op ot h v1 v ↔ v = v') →
  ▷ Φ v' -∗ WP UnOp op ot (Val v1) @ E {{ Φ }}.
Proof.
  iIntros (Hop) "HΦ".
  iApply (wp_unop v'). by move => h; apply Hop.
  iIntros "!#" (v h). rewrite Hop. iIntros (?). subst. by iApply "HΦ".
Qed.

Lemma wp_deref v Φ vl l ly q E:
  val_to_loc vl = Some l →
  l `has_layout_loc` ly →
  v `has_layout_val` ly →
  l↦{q}v -∗ ▷ (l ↦{q} v -∗ Φ v) -∗ WP !{ly} (Val vl) @ E {{ Φ }}.
Proof.
  iIntros (Hl Hll Hlv) "Hmt HΦ".
  iApply wp_lift_head_step; auto.
  iIntros ([h ub fn] ???) "(%&Hhctx&Hfctx)".
  iMod (heap_read_na with "Hhctx Hmt") as "(% & Hσ & Hσclose)" => //.
  iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver. iModIntro.
  iSplit; first by eauto 7 using DerefS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step. iMod "Hclose" as "$". iModIntro. unfold end_st, end_expr.
  have <- : (v = v') by apply: heap_at_inj_val.
  iFrame => /=. iSplit; first by eauto 7 using block_used_agree_heap_upd.
  iApply wp_lift_atomic_head_step_no_fork; auto.
  iIntros ([h2 fn2] ???) "(%&Hhctx&Hfctx)". iMod ("Hσclose" with "Hhctx") as (?) "(Hσ & Hv)".
  iModIntro; iSplit; first by eauto 7 using DerefS.
  iIntros "!#" (e2 σ2 efs Hst) "!#". inv_expr_step.
  have <- : (v = v'0) by apply: heap_at_inj_val.
  iFrame. iSplitR => //=. iSplit; first by eauto 7 using block_used_agree_heap_upd.
  by iApply "HΦ".
Qed.

Lemma wp_cas_fail vl1 vl2 vd vo ve z1 z2 Φ l1 l2 it q E:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` it_layout it →
  l2 `has_layout_loc` it_layout it →
  val_to_int vo it = Some z1 →
  val_to_int ve it = Some z2 →
  length vd = it_length it →
  (it_length it ≤ loc_size)%nat →
  z1 ≠ z2 →
  l1↦{q}vo -∗ l2↦ve -∗ ▷ (l1 ↦{q} vo -∗ l2↦vo -∗ Φ (val_of_bool false)) -∗
   WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Hneq) "Hl1 Hl2 HΦ".
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl1") as %? => //. { naive_solver. }
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl2") as %? => //.
  iModIntro. iSplit; first by eauto 10 using CasFailS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step;
  have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence];
  have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length ve0 = length vo0) by congruence.
  iMod (heap_write with "Hhctx Hl2") as "[$ Hl2]" => //.
  iFrame. iModIntro. rewrite right_id /=.
  iSplit; first by eauto using block_used_agree_heap_upd.
  by iApply ("HΦ" with "Hl1").
Qed.

Lemma wp_cas_suc vl1 vl2 vd vo ve z1 z2 Φ l1 l2 it E q:
  val_to_loc vl1 = Some l1 →
  val_to_loc vl2 = Some l2 →
  l1 `has_layout_loc` it_layout it →
  l2 `has_layout_loc` it_layout it →
  val_to_int vo it = Some z1 →
  val_to_int ve it = Some z2 →
  length vd = it_length it →
  (it_length it ≤ loc_size)%nat →
  z1 = z2 →
  l1↦vo -∗ l2↦{q}ve -∗ ▷ (l1 ↦ vd -∗ l2↦{q}ve -∗ Φ (val_of_bool true)) -∗
   WP CAS (IntOp it) (Val vl1) (Val vl2) (Val vd) @ E {{ Φ }}.
Proof.
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Heq) "Hl1 Hl2 HΦ".
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl1") as %? => //.
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl2") as %? => //. { naive_solver. }
  iModIntro. iSplit; first by eauto 10 using CasSucS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step;
  have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence];
  have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length vo0 = length vd) by congruence.
  iMod (heap_write with "Hhctx Hl1") as "[$ Hmt]" => //.
  iFrame. iModIntro. rewrite right_id /=.
  iSplit; first by eauto using block_used_agree_heap_upd.
  by iApply ("HΦ" with "Hmt").
Qed.

Lemma wp_neg_int Φ v v' n E it:
  val_to_int v it = Some n →
  val_of_int (-n) it = Some v' →
  ▷ Φ (v') -∗ WP UnOp NegOp (IntOp it) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply wp_unop; first eauto using NegOpI.
  iIntros "!#" (v2 h Hop). by inversion Hop; simplify_eq.
Qed.

Lemma wp_cast_int Φ v v' n E its itt:
  val_to_int v its = Some n →
  val_of_int n itt = Some v' →
  ▷ Φ (v') -∗ WP UnOp (CastOp (IntOp itt)) (IntOp its) (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv Hv') "HΦ".
  iApply wp_unop; first eauto using CastOpII.
  iIntros "!#" (v2 h Hop). by inversion Hop; simplify_eq.
Qed.

Lemma wp_cast_loc Φ v l E:
  val_to_loc v = Some l →
  ▷ Φ (val_of_loc l) -∗ WP UnOp (CastOp PtrOp) PtrOp (Val v) @ E {{ Φ }}.
Proof.
  iIntros (Hv) "HΦ".
  iApply wp_unop; first eauto using CastOpPP.
  iIntros "!#" (v2 h Hop). by inversion Hop; simplify_eq.
Qed.

Lemma wp_ptr_offset Φ vl l E it o ly vo:
  val_to_loc vl = Some l →
  val_to_int vo it = Some o →
  0 ≤ o →
  ▷ Φ (val_of_loc (l offset{ly}ₗ o)) -∗ WP Val vl at_offset{ ly , PtrOp, IntOp it} Val vo @ E {{ Φ }}.
Proof.
  iIntros (Hvl Hvo Ho) "HΦ".
  iApply wp_binop; first eauto using PtrOffsetOpIP.
  iIntros "!#" (v h Hbop). by inversion Hbop; simplify_eq.
Qed.

Lemma wp_get_member Φ vl l sl n E:
  val_to_loc vl = Some l →
  is_Some (index_of sl.(sl_members) n) →
  ▷ Φ (val_of_loc (l at{sl}ₗ n)) -∗ WP Val vl at{sl} n @ E {{ Φ }}.
Proof.
  iIntros (Hvl [i Hi]) "HΦ".
  rewrite /GetMember/GetMemberLoc/offset_of Hi /=.
  have [|? Hs]:= (val_of_int_is_some size_t (offset_of_idx sl.(sl_members) i)). {
    split; first by rewrite /it_min/=; lia.
    by apply offset_of_bound.
  }
  rewrite Hs /=. move: Hs => /val_to_of_int Hs.
  iApply wp_binop; first eauto using AddOpPI.
  iIntros "!#" (v h Hbop). by inversion Hbop; simplify_eq.
Qed.

Lemma wp_get_member_union Φ vl l ul n E:
  val_to_loc vl = Some l →
  Φ (val_of_loc (l at_union{ul}ₗ n)) -∗ WP Val vl at_union{ul} n @ E {{ Φ }}.
Proof. iIntros (->%val_of_to_loc) "?". rewrite /GetMemberUnion/GetMemberUnionLoc. by iApply @wp_value. Qed.

Lemma wp_skip Φ v E:
  ▷ Φ v -∗ WP SkipE (Val v) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "[Hhctx Hfctx]".
  iModIntro. iSplit; first by eauto using SkipES.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
    by iFrame.
Qed.

Lemma wp_concat E Φ vs:
  Φ (mjoin vs) -∗ WP Concat (Val <$> vs) @ E {{ Φ }}.
Proof.
  iIntros "HΦ".
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "[Hhctx Hfctx]".
  iModIntro. iSplit; first by eauto using ConcatS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
  by iFrame.
Qed.

Lemma wps_concat_bind_ind vs E Φ es:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Concat (Val <$> (vs ++ vl)) @ E {{ Φ }}) es [] -∗
  WP Concat ((Val <$> vs) ++ es) @ E {{ Φ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: es vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    change (Concat ((Val <$> vs ++ vl2) ++ e :: el))%E with (fill [(ConcatCtx (vs ++ vl2) el)] e).
    iApply @wp_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=. rewrite (cons_middle _ _ el) (assoc app) -(fmap_app _ _ [v]) -(assoc app).
    by iApply IH.
Qed.

Lemma wp_concat_bind E Φ es:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
        (λ vl, WP Concat (Val <$> vl) @ E {{ Φ }}) es [] -∗
  WP Concat es @ E {{ Φ }}.
Proof. by iApply (wps_concat_bind_ind []). Qed.

Lemma wp_struct_init E Φ sl fs:
  foldr (λ '(n, ly) f, (λ vl,
     WP default (Val (replicate (ly_size ly) Poison)) (n' ← n; (list_to_map fs : gmap _ _) !! n')
        @ E {{ v, f (vl ++ [v]) }}))
    (λ vl, Φ (mjoin vl)) sl.(sl_members) [] -∗
  WP StructInit sl fs @ E {{ Φ }}.
Proof.
  iIntros "He". unfold StructInit. iApply wp_concat_bind.
  move: {2 4}[] => vs.
  iInduction (sl_members sl) as [|[o?]?] "IH" forall (vs) => /=. by iApply wp_concat.
  iApply (wp_wand with "He"). iIntros (v') "Hfold". by iApply "IH".
Qed.

End expr_lifting.

(*** Lifting of statements *)
Definition stmt_wp_def `{!refinedcG Σ} (E : coPset) (Q : gmap block_id stmt) (Ψ : val → iProp Σ) (s : stmt) : iProp Σ :=
  (∀ ts Φ, ⌜Q = ts.(ts_rfn).(rf_fn).(f_code)⌝ -∗
           (∀ v, Ψ v -∗ WP (update_stmt ts (Return v)) {{ Φ }}) -∗
    WP (update_stmt ts s) @ E {{ Φ }}).
Definition stmt_wp_aux `{!refinedcG Σ} (E : coPset) (Q : gmap block_id stmt) (Ψ : val → iProp Σ) : seal (@stmt_wp_def Σ _ E Q Ψ). by eexists. Qed.
Definition stmt_wp `{!refinedcG Σ} (E : coPset) (Q : gmap block_id stmt) (Ψ : val → iProp Σ) :
  stmt → iProp Σ := (stmt_wp_aux E Q Ψ).(unseal).
Definition stmt_wp_eq `{!refinedcG Σ} (E : coPset) (Q : gmap block_id stmt) (Ψ : val → iProp Σ) : stmt_wp E Q Ψ = @stmt_wp_def Σ _ E Q Ψ := (stmt_wp_aux E Q Ψ).(seal_eq).

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
  rewrite stmt_wp_unfold. iIntros "Hs" (ts Φ) "HQ HΨ".
  iApply fupd_wp. iApply ("Hs" with "HQ HΨ").
Qed.

Lemma wps_bind Q Ψ Ks e E:
  WP e @ E {{ v, WPs stmt_fill Ks (Val v) @ E {{ Q , Ψ }} }} -∗
     WPs stmt_fill Ks e @ E {{ Q , Ψ }}.
Proof.
  rewrite stmt_wp_unfold.
  iIntros "He" (ts Φ) "#HQ HΨ". iLöb as "IH" forall (e).
  move Hv: (to_val e) => [|]. {
    move => /of_to_val <-.
    iApply fupd_wp. iMod (wp_value_inv' with "He") as "He".
    rewrite stmt_wp_unfold. by iApply "He".
  }
  iApply wp_lift_step_fupd => /=. { apply stmt_to_val_non_ret. by destruct Ks, e. }
  iIntros (σ1 κ _ _) "Hctx".
  (* TODO: figure out if there is a nice lemma such that the unfolding of wp is not needed (similar to wp_val_inv?)*)
  rewrite wp_unfold /wp_pre /= Hv. iMod ("He" $! _ _ [] 0%nat with "Hctx") as (Hred) "He".
  iModIntro. iSplit. 1: iPureIntro; move: Hred => [?[?[?[??]]]]; eauto using StmtExprS.
  iIntros (ts2 σ2 efs Hs). inv_stmt_step.
  iMod ("He" $! _ _ _ with "[//]")as "He". do 2 iModIntro.
  iMod "He" as "($ & He & _)". iModIntro. rewrite right_id update_stmt_update.
  by iApply ("IH" with "He HΨ").
Qed.

Lemma wps_return Q Ψ v:
  Ψ v -∗ WPs (Return (Val v)) {{ Q , Ψ }}.
Proof. rewrite stmt_wp_unfold. iIntros "Hb" (ts Φ) "HQ HΨ". by iApply "HΨ". Qed.

Lemma wps_goto Q Ψ b s:
  Q !! b = Some s →
  ▷ WPs s {{ Q, Ψ }} -∗ WPs Goto b {{ Q , Ψ }}.
Proof.
  rewrite (stmt_wp_unfold (Goto _)) => Hs.
  iIntros "Hb" (ts Φ HQ) "HΨ". subst Q.
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros (σ1 κ _ _) "Hctx". iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver. iModIntro.
  iSplit; first by eauto using GotoS.
  iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step.
  iMod "HE". iModIntro. iFrame. rewrite update_stmt_update stmt_wp_unfold.
  by iApply ("Hb" with "[] HΨ").
Qed.

Lemma wps_skip Q Ψ s:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs SkipS s {{ Q , Ψ }}.
Proof.
  rewrite (stmt_wp_unfold (SkipS _)).
  iIntros "Hb" (ts Φ HQ) "HΨ". subst Q.
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros (σ1 κ _ _) "Hctx". iMod "Hb". iModIntro.
  iSplit; first by eauto using SkipSS.
  iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step.
  iMod "Hb". iModIntro. iFrame. rewrite update_stmt_update stmt_wp_unfold right_id.
  by iApply ("Hb" with "[] HΨ").
Qed.

Lemma wps_exprs Q Ψ s v:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs ExprS (Val v) s {{ Q , Ψ }}.
Proof.
  rewrite (stmt_wp_unfold (ExprS _ _)).
  iIntros "Hb" (ts Φ HQ) "HΨ". subst Q.
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros (σ1 κ _ _) "Hctx". iMod "Hb". iModIntro.
  iSplit; first by eauto using ExprSS.
  iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step.
  iMod "Hb". iModIntro. iFrame. rewrite update_stmt_update stmt_wp_unfold right_id.
  by iApply ("Hb" with "[] HΨ").
Qed.

Lemma wps_annot n A (a : A) Q Ψ s:
  (|={⊤}[∅]▷=>^n WPs s {{ Q, Ψ }}) -∗ WPs AnnotStmt n a s {{ Q , Ψ }}.
Proof.
  iIntros "Hs". iInduction n as [|n] "IH" => /=. by iApply "Hs".
  rewrite /AnnotStmt. iApply wps_skip. by iApply (step_fupd_wand with "Hs IH").
Qed.


(* TODO: extract a funspec similar to typed_function *)
Lemma wps_call Q Ψ r vf vl s f fn:
  val_to_loc vf = Some f →
  Forall2 has_layout_val vl (f_args fn).*2 →
  fntbl_entry f fn -∗ ▷(∀ lsa lsv, ⌜Forall2 has_layout_loc lsa (f_args fn).*2⌝ -∗
     ([∗ list] l; v ∈ lsa; vl, l↦v) -∗ ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) -∗ ∃ Ψ',
          WPs Goto fn.(f_init) {{ (subst_stmt (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> (lsa ++ lsv))) <$> fn.(f_code), Ψ' }} ∗
         (∀ v, Ψ' v -∗
                  ([∗ list] l; v ∈ lsa; fn.(f_args), l↦|v.2|) ∗
                  ([∗ list] l; v ∈ lsv; fn.(f_local_vars), l↦|v.2|) ∗
                  (WPs subst_stmt [r] [v] s {{ Q , Ψ }}))
   ) -∗
   WPs (r <- Val vf with Val <$> vl; s) {{ Q , Ψ }}.
Proof.
  rewrite (stmt_wp_unfold (Call _ _ _ _)).
  move => Hf Hly. iIntros "Hf HWP" (ts Φ ->) "HΨ".
  move: (Hly) => /Forall2_length. rewrite fmap_length => ?.
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros (σ1 κ _ _) "(H&Hhctx&Hfctx)". iDestruct "H" as %Hub.
  iDestruct (fntbl_entry_lookup with "Hfctx Hf") as %Hfn.
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver. iModIntro. iSplit. {
    have [|ls [Hlen [Hfree [HND Hlys]]]] := heap_fresh_blocks (length fn.(f_args) + length fn.(f_local_vars)) σ1.(st_used_blocks) ((f_args fn).*2 ++ (f_local_vars fn).*2). by rewrite !app_length !fmap_length.
    have [lsa [lsv [? [Ha Hv]]]] : (∃ lsa lsv, ls = lsa ++ lsv ∧ length lsa = length fn.(f_args) ∧ length lsv = length fn.(f_local_vars)). {
      exists (take (length fn.(f_args)) ls), (drop (length fn.(f_args)) ls).
      rewrite firstn_skipn take_length_le ?drop_length Hlen; split_and? => //; lia.
    }
    subst ls. move: Hfree => /Forall_app[/Forall_forall ? /Forall_forall?].
    move: Hlys => /Forall2_app_inv[|??]. by rewrite fmap_length.
    iPureIntro. eexists _, _, _, _; simpl.
    eapply (CallS lsa lsv) => //; apply/Forall_forall => ??; try apply Hub;set_solver. }
  iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step.
  match goal with | H : NoDup _ |- _ => rewrite ->fmap_app, NoDup_app in H; revert H end.
  move => [? [? ?]].
  iMod (heap_alloc_list lsv (((λ p, replicate (ly_size p.2) ☠%V) <$> f_local_vars fn)) with "Hhctx") as "[Hhctx Hv]" => //.
  { by rewrite fmap_length. }

  iMod (heap_alloc_list lsa vs with "Hhctx") as "[$ Ha]" => //.
  { apply Forall_forall => [[??]] Hin. apply heap_block_free_upd_list.
    by eapply (Forall_forall _ lsa). set_solver. }
  { by etrans. }
  iDestruct ("HWP" $! lsa lsv with "[//] Ha [Hv]") as (Ψ') "(HQinit & HΨ')". {
    rewrite big_sepL2_fmap_r. iApply (big_sepL2_mono with "Hv") => ??? ?? /=.
    iIntros "?". iExists _. iFrame. iPureIntro. split; first by apply replicate_length.
    apply: Forall2_lookup_lr. 2: done. done. rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
  }
  iMod "HE". iModIntro. iFrame.
  rewrite -(update_stmt_id {| ts_rfn := _; ts_conts := _|}).
  rewrite stmt_wp_unfold. iSplit. {
    iPureIntro => /=.
    apply: block_used_agree_heap_upd_list_in. set_solver.
    apply: block_used_agree_heap_upd_list_in. set_solver.
    move => l' Hl'. apply Hub. set_solver.
  }
  iApply ("HQinit") => //=.
  (** prove Return *)
  iIntros (v) "Hv".
  iDestruct ("HΨ'" with "Hv") as "(Ha & Hv & Hs)".
  iApply wp_lift_step => //=.
  iIntros (σ3 κ2 _ _) "(%&Hhctx&Hfctx)".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver. iModIntro.
  iSplit; first by eauto using ReturnS.
  iIntros "!#" (ts3 σ4 ? Hst). inv_stmt_step.
  iMod "HE" as "$". iFrame. rewrite /heap_fmap/= heap_free_list_app /=.
  rewrite -!(big_sepL2_fmap_r snd (λ _ l ly, l↦|ly|)%I).
  iMod (heap_free_list_free with "Hhctx Hv") as "Hhctx".
  iMod (heap_free_list_free with "Hhctx Ha") as "$". iModIntro.
  rewrite stmt_wp_unfold.
  iSplit; first by eauto using block_used_agree_heap_free_list.
  by iApply "Hs".
Qed.

Lemma wps_assign Q Ψ vl ly vr s l o:
  let E := if o is ScOrd then ∅ else ⊤ in
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  vr `has_layout_val` ly →
  (|={⊤,E}=> l↦|ly| ∗ ▷ (l↦vr ={E,⊤}=∗ WPs s {{Q, Ψ}})) -∗ WPs (Val vl <-{ly, o} Val vr; s) {{ Q , Ψ }}.
Proof.
  move => E Ho Hvl Hly. rewrite (stmt_wp_unfold (Assign _ _ _ _ _)).
  iIntros "HWP" (ts Φ) "#HQ HΨ".
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros ([h1 ?] κ _ _) "(%&Hhctx&Hfctx)".
  iMod "HWP" as "[Hl HWP]". iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
  iDestruct "Hl" as (v' ? ?) "Hl". unfold E. case: Ho => ->.
  - iModIntro.
    iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl") as %? => //.
    iSplit; first by eauto 7 using AssignS.
    iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step. unfold end_val.
    have ? : (length v' = length v2) by congruence.
    iMod (heap_write with "Hhctx Hl") as "[$ Hl]" => //.
    iMod ("HWP" with "Hl") as "HWP".
    iModIntro. iFrame. rewrite update_stmt_update stmt_wp_unfold. rewrite right_id /=.
    iSplit; first by eauto 7 using block_used_agree_heap_upd.
    by iApply ("HWP" with "HQ HΨ").
  - iMod (heap_write_na _ _ _ vr with "Hhctx Hl") as (?) "[Hhctx Hc]" => //. congruence.
    iModIntro. iSplit; first by eauto 10 using AssignS.
    iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step. iMod "HE" as "$".
    have ? : (v' = v'0) by [apply: heap_at_inj_val]; subst v'0.
    iFrame => /=. iModIntro. rewrite update_stmt_update.
    iSplit; first by eauto using block_used_agree_heap_upd.

    iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
    iIntros ([h2 ?] κ _ _) "(%&Hhctx&Hfctx)" => /=. iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
    iMod ("Hc" with "Hhctx") as (?) "[Hhctx Hmt]".
    iModIntro. iSplit; first by eauto 10 using AssignS. unfold end_stmt.
    iIntros "!#" (e2 σ2 efs Hst). inv_stmt_step. iMod "HE" as "$".
    have ? : (v' = v'0) by [apply: heap_at_go_inj_val']; subst v'0.
    iFrame => /=. iMod ("HWP" with "Hmt") as "HWP".
    iModIntro. rewrite update_stmt_update stmt_wp_unfold.
    have ? : (length v' = length v3) by congruence.
    iSplit; first by eauto using block_used_agree_heap_upd.
    by iApply ("HWP" with "HQ HΨ").
Qed.


Lemma wps_switch Q Ψ v n ss def m it:
  val_to_int v it = Some n →
  (∀ i, m !! n = Some i → is_Some (ss !! i)) →
  WPs default def (i ← m !! n; ss !! i) {{ Q, Ψ }} -∗ WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  rewrite (stmt_wp_unfold (Switch _ _ _ _ _)) => Hv Hm. iIntros "HS" (ts Φ) "#HQ HΨ".
  iApply wp_lift_step => /=. 1: by apply stmt_to_val_non_ret.
  iIntros (σ1 κ _ _) "Hctx".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
  iModIntro. iSplit; first by eauto using SwitchS.
  iIntros "!#" (ts3 σ4 ? Hst). inv_stmt_step.
  iMod "HE" as "$". iModIntro. iFrame "Hctx". rewrite update_stmt_update stmt_wp_unfold.
  by iApply "HS".
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
Proof. iIntros (Hv Hn) "Hs". rewrite /notation.Assert. iApply wps_if => //. by case_decide. Qed.

Lemma wps_call_bind_ind vs E Q Ψ r vf el s:
  foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
  (λ vl, WPs (r <- Val vf with Val <$> (vs ++ vl) ; s) @ E {{ Q , Ψ }}) el [] -∗
  WPs (r <- Val vf with (Val <$> vs) ++ el; s) @ E{{ Q , Ψ }}.
Proof.
  rewrite -{2}(app_nil_r vs).
  move: {2 3}[] => vl2.
  elim: el vs vl2 => /=.
  - iIntros (vs vl2) "He". by rewrite !app_nil_r.
  - iIntros (e el IH vs vl2) "Hf".
    change (r <- vf with (Val <$> vs ++ vl2) ++ e :: el; s)%E with (stmt_fill (CallRCtx r vf (vs ++ vl2) el s) e).
    iApply wps_bind. iApply (wp_wand with "Hf").
    iIntros (v) "Hf" => /=.
    rewrite (cons_middle _ _ el) (assoc app) -(fmap_app _ _ [v]) -(assoc app).
    by iApply IH.
Qed.

Lemma wps_call_bind E Q Ψ r ef el s:
  WP ef @ E {{ vf, foldr (λ e f, (λ vl, WP e @ E {{ v, f (vl ++ [v]) }}))
                         (λ vl, WPs (r <- Val vf with Val <$> vl ; s) @ E {{ Q , Ψ }}) el [] }} -∗
  WPs (r <- ef with el; s) @ E{{ Q , Ψ }}.
Proof.
  iIntros "He".
  change (r <- ef with el; s)%E with (stmt_fill (CallLCtx r el s) ef).
  iApply wps_bind. iApply (wp_wand with "He").
  iIntros (v). by iApply (wps_call_bind_ind []).
Qed.


Definition wps_block (P : iProp Σ) (b : block_id) (Q : gmap block_id stmt) (Ψ : val → iProp Σ) : iProp Σ :=
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

(*** Tests *)
Section tests.
  Context `{!refinedcG Σ}.

  Example test_wp_expr ly l (Φ : _ → iProp Σ):
    (⊢ WP (!{ly} l) {{ Φ }}).
  Proof. Abort.

  Example test_wp_stmt (Φ : _ → iProp Σ) fn:
    (⊢ WP ({| ts_rfn := {| rf_fn := fn; rf_locs := []; rf_stmt := Goto "a" |}; ts_conts := []|}) {{ Φ }}).
  Proof. Abort.

  Example test_wps l Q Ψ E :
    (⊢ WPs Return l {{ Q, Ψ }} ∗ WPs Return l @ E {{ Q, Ψ }}).
  Proof. Abort.
End tests.
