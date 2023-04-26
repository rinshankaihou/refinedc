From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes int own struct.
Set Default Proof Using "Type".

Section padded.
  Context `{!typeG Σ}.

  Program Definition padded (ty : type) (lyty ly : layout) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp ly ∧ ty.(ty_has_op_type) (UntypedOp lyty) MCNone ;
    ty_own β l :=
      (⌜lyty ⊑ ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗
      loc_in_bounds l ly.(ly_size) ∗
      l ◁ₗ{β} ty ∗ (l +ₗ lyty.(ly_size)) ◁ₗ{β} uninit (ly_offset ly lyty.(ly_size)))%I;
    ty_own_val v := (∃ v1 v2, ⌜lyty ⊑ ly⌝ ∗ ⌜v = v1 ++ v2⌝ ∗ v1 ◁ᵥ ty ∗ v2 ◁ᵥ uninit (ly_offset ly lyty.(ly_size)))%I;
  |}.
  Next Obligation.
    iDestruct 1 as "[$ [$ [$ [HT Hl]]]]".
    iMod (ty_share with "HT") as "$" => //.
    by iApply ty_share.
  Qed.
  Next Obligation. iIntros (?????? [-> ?]) "[_ [$ _]]". Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt v [-> ?]). iDestruct 1 as (v1 v2 [??] ->) "[Hv1 Hv2]".
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Heq2; [done|].
    iPureIntro. rewrite /has_layout_val app_length Heq1 Heq2 {2}/ly_size/=. lia.
  Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt l [-> ?]). iDestruct 1 as ([??] ?) "[_ [Hl Hpad]]".
    iDestruct (ty_deref with "Hl") as (v1) "[Hmt1 Hv1]"; [done|].
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_deref _ (UntypedOp _) MCNone with "Hpad") as (v2) "[Hmt2 Hv2]"; [done|].
    iExists (v1 ++ v2). rewrite heap_mapsto_app Heq1. iFrame.
    iExists _, _. unfold bytewise; simpl_type. by repeat iSplit => //.
  Qed.
  Next Obligation.
    iIntros (ty lyty ly ot mt l v [-> ?] Hly) "Hmt". iDestruct 1 as (v1 v2 [??] ->) "[Hv1 Hv2]".
    iDestruct (ty_size_eq with "Hv1") as %Heq1; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Heq2; [done|].
    iDestruct (heap_mapsto_loc_in_bounds with "Hmt") as "#Hb".
    rewrite heap_mapsto_app Heq1.
    iDestruct "Hmt" as "[Hmt1 Hmt2]".
    iDestruct (ty_ref with "[%] Hmt1 Hv1") as "$"; [done| by apply: has_layout_loc_trans|].
    iDestruct (ty_ref _ (UntypedOp _) MCNone with "[%] Hmt2 Hv2") as "$" => //. { by apply: has_layout_ly_offset. }
    iSplit => //. iSplit => //. iApply loc_in_bounds_shorten; last done.
    rewrite app_length Heq1 Heq2 /ly_size /= -!/(ly_size _). lia.
  Qed.
  Next Obligation. iIntros (ty lyty ly v ot mt st ?). apply mem_cast_compat_Untyped. destruct ot; naive_solver. Qed.

  Global Instance padded_le : Proper ((⊑) ==> (=) ==> (=) ==> (⊑)) padded.
  Proof. solve_type_proper. Qed.
  Global Instance padded_proper : Proper ((≡) ==> (=) ==> (=) ==> (≡)) padded.
  Proof. solve_type_proper. Qed.

  Global Instance loc_in_bounds_padded ty lyty ly β: LocInBounds (padded ty lyty ly) β (ly_size ly).
  Proof.
    constructor. by iIntros (l) "(_&_&H&_)".
  Qed.

  Global Program Instance learn_align_padded β ty ly lyty
    : LearnAlignment β (padded ty lyty ly) (Some (ly_align ly)).
  Next Obligation. by iIntros (β ty ly lyty l) "(_&%&_)". Qed.

  Lemma simpl_padded_hyp_eq_layout l β ty ly T:
    (l ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} padded ty ly ly) T.
  Proof. iIntros "HT (?&?&?&?&?)". by iApply "HT". Qed.
  Global Instance simpl_padded_hyp_eq_layout_inst l β ty ly:
    SimplifyHypPlace l β (padded ty ly ly) (Some 0%N) :=
    λ T, i2p (simpl_padded_hyp_eq_layout l β ty ly T).
  (* TODO: should this also work for Shr? *)
  Lemma simpl_padded_goal_eq_layout l ty ly T:
    T (⌜ty.(ty_has_op_type) (UntypedOp ly) MCNone⌝ ∗ l ◁ₗ ty) -∗
    simplify_goal (l ◁ₗ padded ty ly ly) T.
  Proof.
    iIntros "HT". iExists _. iFrame. iIntros "[% Hl]". iDestruct (ty_aligned with "Hl") as %?; [done|].
    do 2 iSplit => //. iDestruct (movable_loc_in_bounds with "Hl") as "#Hb"; [done|]. iFrame "Hl Hb".
    iExists []. rewrite heap_mapsto_own_state_nil.
    iSplit. { iPureIntro. rewrite /has_layout_val/ly_offset/ly_size /=. lia. }
    iSplit. { iPureIntro. by apply: has_layout_ly_offset. }
    rewrite -{1}(Nat.add_0_r (ly_size _)) -loc_in_bounds_split.
    by iDestruct "Hb" as "[_$]".
  Qed.
  Global Instance simpl_padded_goal_eq_layout_inst l ty ly:
    SimplifyGoalPlace l Own (padded ty ly ly) (Some 0%N) :=
    λ T, i2p (simpl_padded_goal_eq_layout l ty ly T).

  (* we deliberately introduce a fresh location l because otherwise l
  and l' could get confused and we might have two l ◁ₗ ... for the
  same l in the context. (one with padded (l @ place) ...
  and one with the type in the padded *)
  Lemma type_place_padded K l β1 ty T lyty ly:
    (∀ l', typed_place K l' β1 ty (λ l2 ty2 β typ, T l2 ty2 β (λ t, padded (typ t) lyty ly))) -∗
    typed_place K l β1 (padded ty lyty ly) T.
  Proof.
    iIntros "HP" (Φ) "(% & % & Hb & Hl & Hpad) HΦ" => /=.
    iApply ("HP" with "Hl"). iIntros (l2 β2 ty2 typ R) "Hl2 Hc".
    iApply ("HΦ" with "Hl2"). iIntros (ty') "Hl2".
    iMod ("Hc" with "Hl2") as "[$ $]". by iFrame.
  Qed.
  (* This should have a lower priority than type_place_id *)
  Global Instance type_place_padded_inst K l β1 ty lyty ly :
    TypedPlace K l β1 (padded ty lyty ly) | 50 :=
    λ T, i2p (type_place_padded K l β1 ty T lyty ly).

  (* Only works for Own since ty might have interior mutability, but
  uninit ty assumes that the values are frozen *)
  Lemma subsume_padded_uninit l ly1 ly2 lyty ty T:
    (⌜ty.(ty_has_op_type) (UntypedOp lyty) MCNone⌝ ∗ ∀ v, v ◁ᵥ ty -∗ subsume (l ◁ₗ uninit ly1) (l ◁ₗ uninit ly2) T) -∗
    subsume (l ◁ₗ padded ty lyty ly1) (l ◁ₗ uninit ly2) T.
  Proof.
    iIntros "[% HT]". iDestruct 1 as ([? ?] ?) "(Hb & Hl & Hr)".
    iDestruct (ty_deref with "Hl") as (v1) "[Hl Hv1]"; [done|].
    iDestruct (ty_size_eq with "Hv1") as %Hlen1; [done|].
    iDestruct (ty_deref _ (UntypedOp _) MCNone with "Hr") as (v2) "[Hr Hv2]"; [done|].
    iDestruct (ty_size_eq _ (UntypedOp _) MCNone with "Hv2") as %Hlen2; [done|].
    iApply ("HT" with "Hv1"). iExists (v1 ++ v2).
    rewrite /= heap_mapsto_app /has_layout_val app_length Forall_forall Hlen1 Hlen2.
    iFrame. iPureIntro; split_and! => //.
    rewrite /= /ly_offset {2}/ly_size. lia.
  Qed.
  Global Instance subsume_padded_uninit_inst l ly1 ly2 lyty ty:
    SubsumePlace l Own (padded ty lyty ly1) (uninit ly2) | 4 :=
    λ T, i2p (subsume_padded_uninit l ly1 ly2 lyty ty T).

  Lemma subsume_uninit_padded l β ly lyty T:
    ⌜lyty ⊑ ly⌝ ∗ T -∗
    subsume (l ◁ₗ{β} uninit ly) (l ◁ₗ{β} padded (uninit lyty) lyty ly) T.
  Proof.
    iDestruct 1 as ([? ?]) "$". iIntros "Hl".
    iDestruct (bytewise_loc_in_bounds with "Hl") as "#$".
    iDestruct (split_bytewise with "Hl") as "[Hl $]" => //.
    rewrite /ty_own/=. iDestruct "Hl" as (????) "Hl".
    iSplit; first done. iSplit; first done. iExists _; iFrame.
    iSplit; first done. iSplit; last by rewrite Forall_forall.
    iPureIntro. by apply: has_layout_loc_trans.
  Qed.
  Global Instance subsume_uninit_padded_inst l ly β lyty:
    SubsumePlace l β (uninit ly) (padded (uninit lyty) lyty ly) :=
    λ T, i2p (subsume_uninit_padded l β ly lyty T).

  Lemma type_place_padded_uninit_struct K l β sl n T ly:
    ⌜(layout_of sl) ⊑ ly⌝ ∗
      typed_place (GetMemberPCtx sl n :: K) l β (padded (struct sl (uninit <$> omap (λ '(n, ly), const ly <$> n) sl.(sl_members))) sl ly) T -∗
    typed_place (GetMemberPCtx sl n :: K) l β (uninit ly) T.
  Proof.
    iIntros "[% HT]" (Φ) "Hl".
    iDestruct (apply_subsume_place_true with "Hl []") as "Hl".
    { by iApply (subsume_uninit_padded _ _ _ sl). }
    iApply "HT". iDestruct "Hl" as "[$ [$ [$ [Hl $]]]]". by rewrite uninit_struct_equiv.
  Qed.
  Global Instance type_place_padded_uninit_struct_inst K l β sl n ly :
    TypedPlace (GetMemberPCtx sl n :: K) l β (uninit ly) :=
    λ T, i2p (type_place_padded_uninit_struct K l β sl n T ly).



  (* If lyty is the same, then ly also must be the same. *)
  Lemma padded_mono l β ty1 ty2 T ly1 ly2 lyty:
    ⌜ly1 = ly2⌝ ∗ subsume (l ◁ₗ{β} ty1) (l ◁ₗ{β} ty2) T -∗
    subsume (l ◁ₗ{β} padded ty1 lyty ly1) (l ◁ₗ{β} padded ty2 lyty ly2) T.
  Proof. iIntros "[-> Hsub] ($&$&$&Hl&$)". by iApply "Hsub". Qed.
  Global Instance padded_mono_inst l β ty1 ty2 ly1 ly2 lyty:
    SubsumePlace l β (padded ty1 lyty ly1) (padded ty2 lyty ly2) :=
    λ T, i2p (padded_mono l β ty1 ty2 T ly1 ly2 lyty).

  Lemma split_padded n l β ly1 lyty ty:
    (n ≤ ly1.(ly_size))%nat →
    (lyty.(ly_size) ≤ n)%nat →
    l ◁ₗ{β} padded ty lyty ly1 -∗
      l ◁ₗ{β} padded ty lyty (ly_set_size ly1 n) ∗ (l +ₗ n) ◁ₗ{β} (uninit (ly_offset ly1 n)).
  Proof.
    iIntros (? ?). iDestruct 1 as ([??]?) "(#Hb&$&Hl)".
    (* iDestruct (split_uninit with "Hl") as "[? ?]". *)
    rewrite {1}/ty_own/=. iDestruct "Hl" as (v Hv Hl _) "Hmt".
    rewrite -[v](take_drop (n - lyty.(ly_size))%nat) heap_mapsto_own_state_app.
    iDestruct "Hmt" as "[Hmt1 Hmt2]". iSplitL "Hmt1".
    - iSplit => //. iSplit; first by iPureIntro; apply: has_layout_loc_trans.
      iSplit. { iApply loc_in_bounds_shorten; last done. rewrite /ly_size /= -/(ly_size _). lia. }
      iExists _. iFrame. iPureIntro. rewrite Forall_forall. split_and! => //.
      rewrite /has_layout_val take_length_le // Hv. rewrite {2}/ly_size/=. lia.
    - rewrite shift_loc_assoc take_length_le. 2: rewrite Hv {2}/ly_size/=; lia.
      have ->: (ly_size lyty + (n - ly_size lyty)%nat) = n by lia.
      iExists _. iFrame. iPureIntro. rewrite Forall_forall.
      split_and! => //; last by apply has_layout_ly_offset.
      rewrite /has_layout_val drop_length Hv {1 4}/ly_size/=. lia.
  Qed.


  Lemma type_add_padded v2 β ly lyty ty (p : loc) (n : Z) it T:
    (⌜n ∈ it⌝ -∗ ⌜0 ≤ n⌝ ∗ ⌜Z.to_nat n ≤ ly.(ly_size)⌝%nat ∗ ⌜lyty.(ly_size) ≤ Z.to_nat n⌝%nat ∗ (p ◁ₗ{β} padded ty lyty (ly_set_size ly (Z.to_nat n)) -∗ v2 ◁ᵥ n @ int it -∗
          T (val_of_loc (p +ₗ n)) ((p +ₗ n) @ &frac{β} (uninit (ly_offset ly (Z.to_nat n)))))) -∗
      typed_bin_op v2 (v2 ◁ᵥ n @ int it) p (p ◁ₗ{β} padded ty lyty ly) (PtrOffsetOp u8) (IntOp it) PtrOp T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ".
    move: (Hint) => /val_to_Z_in_range?.
    iDestruct ("HT" with "[//]") as (???) "HT".
    iDestruct (split_padded (Z.to_nat n) with "Hp") as "[H1 H2]"; [lia..|].
    rewrite -!(offset_loc_sz1 u8)// Z2Nat.id; [|lia].
    iDestruct (loc_in_bounds_in_bounds with "H2") as "#?".
    iApply wp_ptr_offset; [ by apply val_to_of_loc | done | |].
    { iApply loc_in_bounds_shorten; [|done]; lia. }
    iModIntro. iApply ("HΦ" with "[H2]"). 2: iApply ("HT" with "H1 []").
    - unfold frac_ptr; simpl_type. by iFrame.
    - by iPureIntro.
  Qed.
  Global Instance type_add_padded_inst v2 β ly lyty ty (p : loc) n it:
    TypedBinOp v2 (v2 ◁ᵥ n @ int it)%I p (p ◁ₗ{β} padded ty lyty ly)%I (PtrOffsetOp u8) (IntOp it) PtrOp :=
    λ T, i2p (type_add_padded v2 β ly lyty ty p n it T).


  Lemma annot_to_uninit_padded l ty ly lyty T:
    (⌜ty.(ty_has_op_type) (UntypedOp lyty) MCNone⌝ ∗ (l ◁ₗ uninit ly -∗ T)) -∗
    typed_annot_stmt ToUninit l (l ◁ₗ padded ty lyty ly) T.
  Proof.
    iIntros "[% HT] Hl". iApply step_fupd_intro => //. iModIntro.
    iDestruct (ty_aligned _ _ MCNone with "Hl") as %?; [done|].
    iDestruct (ty_deref _ _ MCNone with "Hl") as (v) "[Hmt Hv]"; [done|].
    iDestruct (ty_size_eq _ _ MCNone with "Hv") as %?; [done|].
    iApply ("HT").
    iExists v. rewrite Forall_forall. by iFrame.
  Qed.
  Global Instance annot_to_uninit_inst l ty ly lyty:
    TypedAnnotStmt (ToUninit) l (l ◁ₗ padded ty lyty ly) :=
    λ T, i2p (annot_to_uninit_padded l ty ly lyty T).

End padded.
Notation "padded< ty , lyty , ly >" := (padded ty lyty ly)
  (only printing, format "'padded<' ty ,  lyty ,  ly '>'") : printing_sugar.

Global Typeclasses Opaque padded.
