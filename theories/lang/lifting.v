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
Instance deref_atomic s (l : loc) ly : Atomic s (Deref ScOrd ly l).
Proof. solve_atomic. Qed.
Instance use_atomic s (l : loc) ly : Atomic s (Use ScOrd ly l).
Proof. rewrite /Use. solve_atomic. Qed.

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
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "Hctx !>".
  iDestruct ("HΦ" with "Hctx") as ([v' Heval]) "HΦ".
  iSplit; first by eauto using BinOpS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
  iModIntro. rewrite right_id. by iApply "HΦ".
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
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "Hctx !>".
  iDestruct ("HΦ" with "Hctx") as ([v' Heval]) "HΦ".
  iSplit; first by eauto using UnOpS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step.
  iModIntro. rewrite right_id. by iApply "HΦ".
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
  iApply wp_lift_head_step; auto.
  iIntros ([h ub fn] ???) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_has_alloc_id with "Hmt") as %Haid.
  destruct o; try by destruct Ho.
  - iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver. iModIntro.
    iDestruct (heap_mapsto_lookup_q (λ st, ∃ n, st = RSt n) with "Hhctx Hmt") as %Hat. naive_solver.
    iSplit; first by eauto 8 using DerefS.
    iIntros "!#" (e2 σ2 efs Hst). inv_expr_step. iMod "Hclose" as "$". iModIntro. unfold end_st, end_expr.
    have <- : (v = v') by apply: heap_at_inj_val.
    rewrite /heap_fmap/=. erewrite heap_upd_heap_at_id => //.
    iFrame. iSplit => //. iApply @wp_value. by iApply "HΦ".
  - iMod (heap_read_na with "Hhctx Hmt") as "(% & Hσ & Hσclose)" => //.
    iMod (fupd_intro_mask' _ ∅) as "Hclose"; first set_solver. iModIntro.
    iSplit; first by eauto 8 using DerefS.
    iIntros "!#" (e2 σ2 efs Hst). inv_expr_step. iMod "Hclose" as "$". iModIntro. unfold end_st, end_expr.
    have <- : (v = v') by apply: heap_at_inj_val.
    iFrame => /=. iSplit => //.
    iApply wp_lift_atomic_head_step_no_fork; auto.
    iIntros ([h2 fn2] ???) "(%&Hhctx&Hfctx)". iMod ("Hσclose" with "Hhctx") as (?) "(Hσ & Hv)".
    iModIntro; iSplit; first by eauto 8 using DerefS.
    iIntros "!#" (e2 σ2 efs Hst) "!#". inv_expr_step.
    have <- : (v = v'0) by apply: heap_at_inj_val.
    iFrame. iSplitR => //=. by iApply "HΦ".
Qed.

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
  iDestruct (heap_mapsto_has_alloc_id with "Hl1") as %Haid1.
  iDestruct (heap_mapsto_has_alloc_id with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl1") as %? => //. { naive_solver. }
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl2") as %? => //.
  iModIntro. iSplit; first by eauto 12 using CasFailS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step;
  have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence];
  have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length ve0 = length vo0) by congruence.
  iMod (heap_write with "Hhctx Hl2") as "[$ Hl2]" => //.
  iFrame. iModIntro. rewrite right_id /=.
  by iApply ("HΦ" with "Hl1").
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
  iIntros (Hl1 Hl2 Hly1 Hly2 Hvo Hve Hlen1 Hlen2 Heq) "Hl1 Hl2 HΦ".
  iDestruct (heap_mapsto_has_alloc_id with "Hl1") as %Haid1.
  iDestruct (heap_mapsto_has_alloc_id with "Hl2") as %Haid2.
  move: (Hvo) (Hve) => /val_to_int_length ? /val_to_int_length ?.
  iApply wp_lift_atomic_head_step; auto.
  iIntros (σ1 ???) "(%&Hhctx&Hfctx)".
  iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl1") as %? => //.
  iDestruct (heap_mapsto_lookup_q (λ st : lock_state, ∃ n : nat, st = RSt n) with "Hhctx Hl2") as %? => //. { naive_solver. }
  iModIntro. iSplit; first by eauto 12 using CasSucS.
  iIntros "!#" (e2 σ2 efs Hst). inv_expr_step;
  have ? : (ve = ve0) by [apply: heap_at_go_inj_val' => //; congruence];
  have ? : (vo = vo0) by [apply: heap_at_go_inj_val' => //; congruence]; simplify_eq.
  have ? : (length vo0 = length vd) by congruence.
  iMod (heap_write with "Hhctx Hl1") as "[$ Hmt]" => //.
  iFrame. iModIntro. rewrite right_id /=.
  by iApply ("HΦ" with "Hmt").
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
  rewrite Ho /= Hs /=. iApply @wp_value.
  by iApply "HΦ".
Qed.

Lemma wp_offset_of_union Φ ul m E:
  Φ (i2v 0 size_t) -∗ WP OffsetOfUnion ul m @ E {{ Φ }}.
Proof. by iApply @wp_value. Qed.

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
     WP default (Val (replicate (ly_size ly) MPoison)) (n' ← n; (list_to_map fs : gmap _ _) !! n')
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
Definition stmt_wp_def `{!refinedcG Σ} (E : coPset) (Q : gmap label stmt) (Ψ : val → iProp Σ) (s : stmt) : iProp Σ :=
  (∀ ts, ⌜ts.(ts_alloc_failure) = false⌝ -∗ ⌜Q = ts.(ts_rfn).(rf_fn).(f_code)⌝ -∗
           (∀ v, Ψ v -∗ WP (update_stmt ts (Return v)) {{ _, True }}) -∗
    WP (update_stmt ts s) @ E {{ _, True }}).
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
  rewrite stmt_wp_unfold. iIntros "Hs" (ts Hts HQ) "HΨ".
  iApply fupd_wp. by iApply "Hs".
Qed.

Lemma wps_wand s E Q Φ Ψ:
  WPs s @ E {{ Q , Φ }} -∗ (∀ v, Φ v -∗ Ψ v) -∗ WPs s @ E {{ Q , Ψ }}.
Proof.
  rewrite !stmt_wp_unfold. iIntros "HΦ H" (???) "HΨ".
  iApply "HΦ"; [done | done | ..]. iIntros (v) "Hv".
  iApply "HΨ". iApply "H". iApply "Hv".
Qed.

Lemma wp_lift_stmt_step E s ts1:
  ((∀ (v : val), s ≠ Return v) ∨ ts1.(ts_conts) ≠ []) →
  (ts1.(ts_alloc_failure) = false) →
  (∀ (σ1 : state), state_ctx σ1 ={E,∅}=∗
     ⌜∃ os ts2 σ2 tsl, simple_stmt_step (update_stmt ts1 s) σ1 os ts2 σ2 tsl ∧
                       (σ1.(st_alloc_failure) = true → σ2.(st_alloc_failure) = true)⌝ ∗
     (∀ os ts2 σ2 tsl, ⌜simple_stmt_step (update_stmt ts1 s) σ1 os ts2 σ2 tsl⌝
        ={∅}=∗ ▷ (|={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗
                  (⌜ts2.(ts_alloc_failure) = false⌝ -∗ WP ts2 @ E {{ _, True }}))))
    -∗ WP update_stmt ts1 s @ E {{ _, True }}.
Proof.
  iIntros (Hnoret ?) "HWP".
  iApply wp_lift_step_fupd. {
    destruct s; destruct ts1 as [??[]] => //.
    destruct e, ts_conts => //. naive_solver.
  }
  iIntros (σ1 κ κs n) "Hσ".
  iMod ("HWP" $! σ1 with "Hσ") as (Hstep) "HWP".
  iModIntro. iSplit. {
    iPureIntro. destruct Hstep as (?&?&?&?&?&?).
    destruct σ1.(st_alloc_failure) eqn:?; eauto using SStep_fail, SStep_ok.
  }
  clear Hstep. iIntros (??? Hstep). inversion Hstep; simplify_eq; simpl.
  all: iMod ("HWP" with "[//]") as "HWP".
  all: do 2 iModIntro.
  all: iMod "HWP" as (->) "[$ HWP]"; iModIntro => /=; rewrite right_id.
  - destruct (ts_alloc_failure e2) eqn:Hfail; last by iApply "HWP".
    iApply wp_value; last done. rewrite /IntoVal /=.
    apply language.of_to_val. by destruct e2 as [??[]].
  - iApply wp_value; last done. rewrite /IntoVal /=.
    apply language.of_to_val. by destruct ts' as [???].
Qed.

Lemma wps_lift_stmt_step E Q Φ s:
  (∀ ts1, ⌜ts1.(ts_alloc_failure) = false⌝ -∗ ⌜Q = ts1.(ts_rfn).(rf_fn).(f_code)⌝ -∗
    ⌜∀ (v : val), s ≠ Return v⌝ ∗
    (∀ (σ1 : state),
      state_ctx σ1 ={E,∅}=∗
        ⌜∃ os ts2 σ2 tsl, simple_stmt_step (update_stmt ts1 s) σ1 os ts2 σ2 tsl ∧
                       (σ1.(st_alloc_failure) = true → σ2.(st_alloc_failure) = true)⌝ ∗
        (∀ os ts2 σ2 tsl, ⌜simple_stmt_step (update_stmt ts1 s) σ1 os ts2 σ2 tsl⌝ ={∅}=∗
           ▷ (|={∅,E}=> ⌜tsl = []⌝ ∗ state_ctx σ2 ∗
              (⌜ts2.(ts_alloc_failure) = false⌝ -∗
               WPs ts2.(ts_rfn).(rf_stmt) @ E {{ ts2.(ts_rfn).(rf_fn).(f_code), (λ v,
                 (∀ v0 : val, Φ v0 -∗ WP update_stmt ts1 (Return v0) {{ _, True }}) -∗
             WP update_stmt ts2 (Return v) {{ _, True }} ) }})))))
    -∗ WPs s @ E {{ Q , Φ }}.
Proof.
  iIntros "HWP". rewrite stmt_wp_unfold. iIntros (ts ? ->) "HΦ".
  iDestruct ("HWP" $! ts with "[//] [//]") as (Hnoretval) "HWP".
  iApply wp_lift_stmt_step => //; first by left. iIntros (σ1) "Hσ".
  iMod ("HWP" with "Hσ") as (?) "HWP". iModIntro. iSplit => //.
  iIntros (os ts2 σ2 tsl Hstep). iMod ("HWP" with "[//]") as "HWP".
  iIntros "!> !>". iMod "HWP" as (?) "[Hσ HWP]".
  iModIntro. iFrame. iSplit => //. iIntros (?).
  rewrite stmt_wp_unfold -(update_stmt_id ts2). iApply "HWP" => //.
  iIntros (v) "HRet". rewrite update_stmt_update. by iApply "HRet".
Qed.

Lemma wps_bind Q Ψ Ks e E:
  WP e @ E {{ v, WPs stmt_fill Ks (Val v) @ E {{ Q , Ψ }} }} -∗
     WPs stmt_fill Ks e @ E {{ Q , Ψ }}.
Proof.
  iIntros "He". iLöb as "IH" forall (e).
  move Hv: (to_val e) => [|]. {
    move => /of_to_val <-. rewrite wp_value_fupd'. by iApply fupd_wps.
  }
  iApply wps_lift_stmt_step.
  iIntros (?? ->). iSplit. {
    iPureIntro. move => v. destruct Ks; try done. simpl. move => [Heq]. subst.
    by rewrite to_of_val in Hv.
  }
  iIntros (σ1) "Hctx".
  (* TODO: figure out if there is a nice lemma such that the unfolding of wp is not needed (similar to wp_val_inv?)*)
  rewrite wp_unfold /wp_pre /= Hv.
  iMod ("He" $! _ [] [] 0%nat with "Hctx") as (Hred) "He".
  iModIntro. iSplit; first iPureIntro. {
    move: Hred => [?[?[?[? Hstep]]]]. eexists _, _, _, _. split; first by eauto 10 using StmtExprS.
    destruct Hstep as [? e1]; simplify_eq/=.
    by destruct e1; inv_expr_step.
  }
  iIntros ([] σ2 efs Hs) => //. iIntros (Hstep). inv_stmt_step.
  iMod ("He" $! _ _ _ with "[//]") as "He".
  iModIntro. iNext. iMod "He" as "($ & He & _)". iModIntro.
  iSplit; first done. iIntros (?). iDestruct ("IH" with "He") as "H".
  iApply (wps_wand with "H").
  iIntros (v) "HΨ HWP". rewrite !update_stmt_update. by iApply "HWP".
Qed.

Lemma wps_return Q Ψ v:
  Ψ v -∗ WPs (Return (Val v)) {{ Q , Ψ }}.
Proof. rewrite stmt_wp_unfold. iIntros "Hb" (ts Φ) "HQ HΨ". by iApply "HΨ". Qed.

Lemma wps_goto Q Ψ b s:
  Q !! b = Some s →
  ▷ WPs s {{ Q, Ψ }} -∗ WPs Goto b {{ Q , Ψ }}.
Proof.
  iIntros (Hs) "HWP". iApply wps_lift_stmt_step. iIntros (?? ->).
  iSplit; first done. iIntros (?) "Hσ".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first by set_solver. iModIntro.
  iSplit; first by eauto 10 using GotoS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext.
  iMod "HE" as "_". iModIntro. iSplit; first done. iFrame.
  iIntros (?). iApply (wps_wand with "HWP").
  iIntros (v) "HΨ HWP". rewrite !update_stmt_update. by iApply "HWP".
Qed.

Lemma wps_skip Q Ψ s:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs SkipS s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". iApply wps_lift_stmt_step. iIntros (?? ->).
  iSplit; first done. iIntros (?) "Hσ". iMod "HWP". iModIntro.
  iSplit; first by eauto 10 using SkipSS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext.
  iMod "HWP". iModIntro. iSplit; first done. iFrame.
  iIntros (?). iApply (wps_wand with "HWP").
  iIntros (v) "HΨ HWP". rewrite !update_stmt_update. by iApply "HWP".
Qed.

Lemma wps_exprs Q Ψ s v:
  (|={⊤}[∅]▷=> WPs s {{ Q, Ψ }}) -∗ WPs ExprS (Val v) s {{ Q , Ψ }}.
Proof.
  iIntros "HWP". iApply wps_lift_stmt_step. iIntros (?? ->).
  iSplit; first done. iIntros (?) "Hσ". iMod "HWP". iModIntro.
  iSplit; first by eauto 10 using ExprSS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext.
  iMod "HWP". iModIntro. iSplit; first done. iFrame.
  iIntros (?). iApply (wps_wand with "HWP").
  iIntros (v) "HΨ HWP". rewrite !update_stmt_update. by iApply "HWP".
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
  move => Hf Hly. move: (Hly) => /Forall2_length. rewrite fmap_length => Hlen_vs.
  iIntros "Hf HWP". iApply wps_lift_stmt_step. iIntros (?? ->). iSplit; first done.
  iIntros (σ1) "(H&Hhctx&Hbctx&Hfctx)". iDestruct "H" as %Hub.
  iDestruct (fntbl_entry_lookup with "Hfctx Hf") as %Hfn.
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver. iModIntro.
  iSplit. { eauto 8 using CallFailS. }
  iIntros (???? Hstep). inv_stmt_step; last first. {
    (* Alloc failure case. *)
    iIntros "!> !>". iMod "HE" as "_". iIntros "!>". iSplit; first done.
    rewrite /state_ctx. iFrame. by iIntros (?).
  }
  iMod (heap_alloc_new_blocks_upd with "[$Hhctx $Hbctx $Hfctx]") as "[Hctx Hlv]" => //.
  iMod (heap_alloc_new_blocks_upd with "Hctx") as "[Hctx Hla]" => //.
  iModIntro. iNext.

  iDestruct ("HWP" $! lsa lsv with "[//] Hla [Hlv]") as (Ψ') "(HQinit & HΨ')". {
    rewrite big_sepL2_fmap_r. iApply (big_sepL2_mono with "Hlv") => ??? ?? /=.
    iIntros "?". iExists _. iFrame. iPureIntro. split; first by apply replicate_length.
    apply: Forall2_lookup_lr. 2: done. done. rewrite list_lookup_fmap. apply fmap_Some. naive_solver.
  }
  iMod "HE" as "_". iModIntro. iSplit; first done. iFrame. iIntros (_).
  iApply (wps_wand with "HQinit").
  (** prove Return *)
  iIntros (v) "Hv HWP". iDestruct ("HΨ'" with "Hv") as "(Ha & Hv & Hs)".
  iApply wp_lift_stmt_step => //; first by right.
  iIntros (σ3) "(%&Hhctx&Hfctx)".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver. iModIntro.
  iSplit; first by eauto 8 using ReturnS.
  iIntros (os ts3 σ2' ? Hst). inv_stmt_step. iIntros "!> !>".
  iMod "HE" as "$". iFrame. rewrite /heap_fmap/= heap_free_list_app /=.
  rewrite -!(big_sepL2_fmap_r snd (λ _ l ly, l↦|ly|)%I).
  iMod (heap_free_list_free with "Hhctx Hv") as "Hhctx".
  iMod (heap_free_list_free with "Hhctx Ha") as "$".
  iModIntro.
  rewrite stmt_wp_unfold. iSplit => //.
  iIntros "_". iApply "Hs" => //. iIntros (v) "HΨ".
  destruct ts1 as [??[]] => //. by iApply "HWP".
Qed.

Lemma wps_assign Q Ψ vl ly vr s l o:
  let E := if o is ScOrd then ∅ else ⊤ in
  o = ScOrd ∨ o = Na1Ord →
  val_to_loc vl = Some l →
  vr `has_layout_val` ly →
  (|={⊤,E}=> l↦|ly| ∗ ▷ (l↦vr ={E,⊤}=∗ WPs s {{Q, Ψ}}))
    -∗ WPs (Val vl <-{ly, o} Val vr; s) {{ Q , Ψ }}.
Proof.
  iIntros (E Ho Hvl Hly) "HWP". iApply wps_lift_stmt_step. iIntros (ts ? ->).
  iSplit; first done. iIntros ([h1 ?]) "(%&Hhctx&Hfctx)". iMod "HWP" as "[Hl HWP]".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
  iDestruct "Hl" as (v' ? ?) "Hl".
  iDestruct (heap_mapsto_has_alloc_id with "Hl") as %Haid.
  unfold E. case: Ho => ->.
  - iModIntro.
    iDestruct (heap_mapsto_lookup_1 (λ st : lock_state, st = RSt 0%nat) with "Hhctx Hl") as %? => //.
    iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hstep). inv_stmt_step. unfold end_val.
    have ? : (length v' = length v2) by congruence.
    iMod (heap_write with "Hhctx Hl") as "[$ Hl]" => //.
    iIntros "!> !>". iMod ("HWP" with "Hl") as "HWP".
    iModIntro => /=. iSplit; first done. iFrame. iIntros (?).
    rewrite update_stmt_update /=. iApply (wps_wand with "HWP").
    iIntros (v) "HΨ HWP". rewrite update_stmt_update. by iApply "HWP".
  - iMod (heap_write_na _ _ _ vr with "Hhctx Hl") as (?) "[Hhctx Hc]" => //; first by congruence.
    iModIntro. iSplit; first by eauto 12 using AssignS.
    iIntros (? e2 σ2 efs Hst). inv_stmt_step.
    have ? : (v' = v'0) by [apply: heap_at_inj_val]; subst v'0.
    iFrame => /=. iModIntro. iNext. iMod "HE" as "_". iModIntro. iSplit; first done.
    rewrite update_stmt_update.

    iIntros (?). iApply wps_lift_stmt_step. iIntros (???). iSplit; first done.
    iIntros ([h2 ?]) "(%&Hhctx&Hfctx)" => /=.
    iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
    iMod ("Hc" with "Hhctx") as (?) "[Hhctx Hmt]".
    iModIntro. iSplit; first by eauto 12 using AssignS. unfold end_stmt.
    iIntros (? e2 σ2 efs Hst). inv_stmt_step. iModIntro. iNext. iMod "HE" as "_".
    have ? : (v' = v'0) by [apply: heap_at_go_inj_val']; subst v'0.
    iFrame => /=. iMod ("HWP" with "Hmt") as "HWP".
    iModIntro. rewrite update_stmt_update. iSplit; first done.
    have ? : (length v' = length v3) by congruence.
    iIntros (?). subst end_stmt0. rewrite H8. iApply (wps_wand with "HWP").
    iIntros (v) "HΨ HWP". rewrite update_stmt_update. iApply "HWP".
    iIntros "HWP". rewrite update_stmt_update. by iApply "HWP".
Qed.

Lemma wps_switch Q Ψ v n ss def m it:
  val_to_int v it = Some n →
  (∀ i, m !! n = Some i → is_Some (ss !! i)) →
  WPs default def (i ← m !! n; ss !! i) {{ Q, Ψ }} -∗ WPs (Switch it (Val v) m ss def) {{ Q , Ψ }}.
Proof.
  iIntros (Hv Hm) "HWP". iApply wps_lift_stmt_step. iIntros (?? ->).
  iSplit; first done. iIntros (?) "Hσ".
  iMod (fupd_intro_mask' _ ∅) as "HE"; first set_solver.
  iModIntro. iSplit; first by eauto 8 using SwitchS.
  iIntros (???? Hstep). inv_stmt_step. iModIntro. iNext. iMod "HE" as "_".
  iModIntro. iSplit; first done. iFrame "Hσ". iIntros (_).
  iApply (wps_wand with "HWP"). iIntros (v) "HΨ HWP".
  rewrite !update_stmt_update. by iApply "HWP".
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
