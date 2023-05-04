From lithium Require Import simpl_classes.
From caesium Require Export bitfield.
From refinedc.typing Require Import programs boolean int.
From refinedc.typing Require Export type.
Set Default Proof Using "Type".

Section bitfield_raw.
  Context `{!typeG Σ}.

  Program Definition bitfield_raw_type (it : int_type) (bv : Z) : type := {|
    ty_has_op_type ot mt := is_int_ot ot it;
    ty_own β l := (l ◁ₗ{β} bv @ int it)%I;
    ty_own_val v := (v ◁ᵥ bv @ int it)%I
  |}%I.
  Next Obligation.
    intros. by iApply ty_share.
  Qed.
  Next Obligation.
    intros. iIntros "Hl". by iApply (ty_aligned with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_size_eq with "Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hl". by iApply (ty_deref with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hly Hl Hv". by iApply (ty_ref with "Hly Hl Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_memcast_compat with "Hv").
  Qed.

  Definition bitfield_raw (it : int_type) : rtype :=
    RType (bitfield_raw_type it).

  Global Program Instance bitfield_raw_copyable bv it : Copyable (bv @ bitfield_raw it).
  Next Obligation. move => ???. unfold bitfield_raw; simpl_type. apply _. Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (copy_shr_acc with "Hl").
  Qed.

End bitfield_raw.
Notation "bitfield_raw< it >" := (bitfield_raw it) (only printing, format "'bitfield_raw<' it '>'") : printing_sugar.

Section bitfield.

  Class BitfieldDesc (R : Type) : Type := {
    bitfield_it : int_type;
    bitfield_repr : R → Z;
    bitfield_wf : R → Prop;
  }.

  Context `{!typeG Σ}.

  Program Definition bitfield_type (R : Type) `{BitfieldDesc R} (bv : R) : type := {|
    ty_has_op_type ot mt := is_int_ot ot bitfield_it;
    ty_own β l := (l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it)%I;
    ty_own_val v := (v ◁ᵥ bitfield_repr bv @ int bitfield_it)%I
  |}%I.
  Next Obligation.
    intros. by iApply ty_share.
  Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (ty_aligned with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_size_eq with "Hv").
  Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (ty_deref with "Hl").
  Qed.
  Next Obligation.
    intros. iIntros "Hly Hl Hv". by iApply (ty_ref with "Hly Hl Hv").
  Qed.
  Next Obligation.
    intros. iIntros "Hv". by iApply (ty_memcast_compat with "Hv").
  Qed.

  Definition bitfield (R : Type) `{BitfieldDesc R} : rtype :=
    RType (bitfield_type R).

  Global Program Instance bitfield_copyable R `{BitfieldDesc R} bv : Copyable (bv @ bitfield R).
  Next Obligation. move => ????. unfold bitfield; simpl_type. apply _. Qed.
  Next Obligation.
    intros. rewrite /ty_own /=. iIntros "Hl". by iApply (copy_shr_acc with "Hl").
  Qed.
End bitfield.
Notation "bitfield< R >" := (bitfield R) (only printing, format "'bitfield<' R '>'") : printing_sugar.

Global Typeclasses Opaque bitfield_raw_type.
Global Typeclasses Opaque bitfield_type.

Section programs.
  Context `{!typeG Σ}.

  (* int ↔ bitfield_raw *)

  Lemma subsume_val_int_bitfield_raw T it v n bv :
    (⌜n = bv⌝ ∗ T) ⊢ subsume (v ◁ᵥ n @ int it) (v ◁ᵥ bv @ bitfield_raw it) T.
  Proof.
    by iIntros "[-> $] ?".
  Qed.
  Global Instance subsume_val_int_bitfield_raw_inst it v n bv : SubsumeVal v (n @ int it) (bv @ bitfield_raw it) :=
    λ T, i2p (subsume_val_int_bitfield_raw T it v n bv).

  Lemma subsume_val_bitfield_raw_int T it v n bv :
    (⌜bv = n⌝ ∗ T) ⊢ subsume (v ◁ᵥ bv @ bitfield_raw it) (v ◁ᵥ n @ int it) T.
  Proof.
    by iIntros "[-> $] ?".
  Qed.
  Global Instance subsume_val_bitfield_raw_int_inst it v n bv : SubsumeVal v (bv @ bitfield_raw it) (n @ int it) :=
    λ T, i2p (subsume_val_bitfield_raw_int T it v n bv).

  (* typing rules for bitfield_raw *)

  Lemma type_arithop_bitfield_raw it v1 bv1 v2 bv2 T bv op:
    int_arithop_result it bv1 bv2 op = Some bv →
    (⌜bv1 ∈ it⌝ -∗ ⌜bv2 ∈ it⌝ -∗ ⌜int_arithop_sidecond it bv1 bv2 bv op⌝ ∗
      (tactic_hint (normalize_bitfield bv) (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ bv1 @ bitfield_raw it) v2 (v2 ◁ᵥ bv2 @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT Hv1 Hv2". unfold tactic_hint, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //. iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
  Qed.
  Global Program Instance type_and_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I AndOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw it v1 bv1 v2 bv2 T (Z.land bv1 bv2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_or_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I OrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw it v1 bv1 v2 bv2 T (Z.lor bv1 bv2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_xor_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I XorOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw it v1 bv1 v2 bv2 T (Z.lxor bv1 bv2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shl_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw it v1 bv1 v2 bv2 T (bv1 ≪ bv2) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shr_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw it v1 bv1 v2 bv2 T (bv1 ≫ bv2) _ _).
  Next Obligation. done. Qed.

  Lemma type_not_bitfield_raw bv it v T:
    let bv' := if it_signed it then Z.lnot bv else Z_lunot (bits_per_int it) bv in
    (⌜bv ∈ it⌝ -∗ T (i2v bv' it) (bv' @ bitfield_raw it))
    ⊢ typed_un_op v (v ◁ᵥ bv @ bitfield_raw it)%I (NotIntOp) (IntOp it) T.
  Proof.
    iIntros "HT Hv".
    iApply type_val_expr_mono_strong.
    iApply (type_not_int with "[HT] Hv") => //.
    iIntros "Hbv".
    iDestruct ("HT" with "Hbv") as "?".
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
  Qed.
  Global Instance type_not_bitfield_raw_inst bv it v:
    TypedUnOpVal v (bv @ bitfield_raw it)%I NotIntOp (IntOp it) :=
    λ T, i2p (type_not_bitfield_raw bv it v T).

  Lemma type_relop_bitfield_raw it v1 bv1 v2 bv2 T b op :
    match op with
    | EqOp rit => Some (bool_decide (bv1 = bv2), rit)
    | NeOp rit => Some (bool_decide (bv1 ≠ bv2), rit)
    | LtOp rit => Some (bool_decide (bv1 < bv2), rit)
    | GtOp rit => Some (bool_decide (bv1 > bv2), rit)
    | LeOp rit => Some (bool_decide (bv1 <= bv2), rit)
    | GeOp rit => Some (bool_decide (bv1 >= bv2), rit)
    | _ => None
    end = Some (b, i32) →
    (⌜bv1 ∈ it⌝ -∗ ⌜bv2 ∈ it⌝ -∗ T (i2v (bool_to_Z b) i32) (b @ boolean i32))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ bv1 @ bitfield_raw it) v2 (v2 ◁ᵥ bv2 @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT Hv1 Hv2".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "?".
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
  Qed.
  Global Program Instance type_eq_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I (EqOp i32) (IntOp it) (IntOp it) :=
      λ T, i2p (type_relop_bitfield_raw it v1 bv1 v2 bv2 T (bool_decide (bv1 = bv2)) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_ne_bitfield_raw_inst it v1 bv1 v2 bv2:
    TypedBinOpVal v1 (bv1 @ bitfield_raw it)%I v2 (bv2 @ bitfield_raw it)%I (NeOp i32) (IntOp it) (IntOp it) :=
      λ T, i2p (type_relop_bitfield_raw it v1 bv1 v2 bv2 T (bool_decide (bv1 ≠ bv2)) _ _).
  Next Obligation. done. Qed.

  (* bitfield_raw with int *)

  Lemma type_arithop_bitfield_raw_int it v1 bv v2 n T bv' op:
    int_arithop_result it bv n op = Some bv' →
    (⌜bv ∈ it⌝ -∗ ⌜n ∈ it⌝ -∗ ⌜int_arithop_sidecond it bv n bv' op⌝ ∗
      (tactic_hint (normalize_bitfield bv') (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
     ⊢ typed_bin_op v1 (v1 ◁ᵥ bv @ bitfield_raw it) v2 (v2 ◁ᵥ n @ int it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT Hv1 Hv2". unfold tactic_hint, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //.
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
  Qed.
  Global Program Instance type_shl_bitfield_raw_int_inst it v1 bv v2 n :
    TypedBinOpVal v1 (bv @ bitfield_raw it)%I v2 (n @ int it)%I ShlOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw_int it v1 bv v2 n T (bv ≪ n) _ _).
  Next Obligation. done. Qed.
  Global Program Instance type_shr_bitfield_raw_int_inst it v1 bv v2 n :
    TypedBinOpVal v1 (bv @ bitfield_raw it)%I v2 (n @ int it)%I ShrOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_bitfield_raw_int it v1 bv v2 n T (bv ≫ n) _ _).
  Next Obligation. done. Qed.

  Lemma type_arithop_int_bitfield_raw it v1 n v2 bv T bv' op:
    int_arithop_result it n bv op = Some bv' →
    (⌜n ∈ it⌝ -∗ ⌜bv ∈ it⌝ -∗ ⌜int_arithop_sidecond it n bv bv' op⌝ ∗
      (tactic_hint (normalize_bitfield bv') (λ norm, T (i2v norm it) (norm @ bitfield_raw it))))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ n @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) op (IntOp it) (IntOp it) T.
  Proof.
    iIntros "%Hop HT Hv1 Hv2". unfold tactic_hint, normalize_bitfield.
    iApply type_val_expr_mono_strong.
    iApply (type_arithop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "Hbv1 Hbv2".
    iDestruct ("HT" with "Hbv1 Hbv2") as "[% ?]".
    iSplitR => //.
    iExists _. iFrame. unfold bitfield_raw; simpl_type. iIntros "$".
  Qed.
  Global Program Instance type_and_int_bitfield_raw_inst it v1 n v2 bv :
    TypedBinOpVal v1 (n @ int it)%I v2 (bv @ bitfield_raw it)%I AndOp (IntOp it) (IntOp it) := λ T, i2p (type_arithop_int_bitfield_raw it v1 n v2 bv T (Z.land n bv) _ _).
  Next Obligation. done. Qed.

  Lemma type_bitfield_raw_is_false it v1 v2 bv T :
    (∃ a b, ⌜bv = bf_cons a 1 (bool_to_Z b) bf_nil⌝ ∗ ⌜0 ≤ a⌝ ∗ T (i2v (bool_to_Z (negb b)) i32) ((bool_to_Z (negb b) @ int i32)))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ 0 @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) (EqOp i32) (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2".
    iDestruct "HT" as (a b Hbv ?) "HT".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "_ _".
    have -> : negb b = bool_decide (0 = bv).
    { rewrite (bool_decide_ext _ (bv = 0)) //.
      rewrite Hbv (bool_decide_ext _ (b = false)); last by apply bf_cons_bool_singleton_false_iff.
      by destruct b. }
    iExists _. iFrame. unfold boolean, int; simpl_type. iIntros "(%n&%&%Heq)". move: Heq => /= ?. subst n. done.
  Qed.
  Global Instance type_bitfield_raw_is_false_inst it v1 v2 bv :
    TypedBinOpVal v1 (0 @ int it)%I v2 (bv @ bitfield_raw it)%I (EqOp i32) (IntOp it) (IntOp it) :=
      λ T, i2p (type_bitfield_raw_is_false it v1 v2 bv T).

  Lemma type_bitfield_raw_is_true it v1 v2 bv T :
    (∃ a b, ⌜bv = bf_cons a 1 (bool_to_Z b) bf_nil⌝ ∗ ⌜0 ≤ a⌝ ∗ T (i2v (bool_to_Z b) i32) ((bool_to_Z b) @ int i32))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ 0 @ int it) v2 (v2 ◁ᵥ bv @ bitfield_raw it) (NeOp i32) (IntOp it) (IntOp it) T.
  Proof.
    iIntros "HT Hv1 Hv2".
    iDestruct "HT" as (a b Hbv ?) "HT".
    iApply type_val_expr_mono_strong.
    iApply (type_relop_int_int with "[HT] Hv1 Hv2") => //.
    iIntros "_ _".
    have -> : b = bool_decide (0 ≠ bv).
    { rewrite (bool_decide_ext _ (bv ≠ 0)) //.
      rewrite Hbv (bool_decide_ext _ (b = true)); last by apply bf_cons_bool_singleton_true_iff.
      by destruct b. }
    iExists _. iFrame. unfold boolean, int; simpl_type.
    iIntros "(%n&%&%Heq)". move: Heq => /= ?. subst n. done.
  Qed.
  Global Instance type_bitfield_raw_is_true_inst it v1 v2 bv :
    TypedBinOpVal v1 (0 @ int it)%I v2 (bv @ bitfield_raw it)%I (NeOp i32) (IntOp it) (IntOp it) :=
      λ T, i2p (type_bitfield_raw_is_true it v1 v2 bv T).

  Lemma type_if_bitfield_raw it n v T1 T2:
    destruct_hint (DHintDecide (n ≠ 0)) (DestructHintIfInt n)
      (if decide (n ≠ 0) then T1 else T2)
    ⊢ typed_if (IntOp it) v (v ◁ᵥ n @ bitfield_raw it) T1 T2.
  Proof. unfold bitfield_raw; simpl_type. apply type_if_int. Qed.
  Global Instance type_if_bitfield_inst n v it :
    TypedIf (IntOp it) v (v ◁ᵥ n @ bitfield_raw it)%I :=
    λ T1 T2, i2p (type_if_bitfield_raw it n v T1 T2).

  (* typing rules for bitfield: unfold to bitfield_raw *)

  Lemma simplify_hyp_place_bitfield l β R `{BitfieldDesc R} bv T :
    (l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it -∗ T)
    ⊢ simplify_hyp (l ◁ₗ{β} bv @ bitfield R) T.
  Proof. done. Qed.
  Global Instance simplify_hyp_place_bitfield_inst l β R `{BitfieldDesc R} bv :
    SimplifyHyp (l ◁ₗ{β} bv @ bitfield R)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_bitfield l β R bv T).

  Lemma simplify_goal_place_bitfield l β R `{BitfieldDesc R} bv T :
    T (l ◁ₗ{β} bitfield_repr bv @ bitfield_raw bitfield_it)
    ⊢ simplify_goal (l ◁ₗ{β} bv @ bitfield R) T.
  Proof.
    iIntros "HT". iExists _. iFrame. by iIntros "?".
  Qed.
  Global Instance simplify_goal_place_bitfield_inst l β R `{BitfieldDesc R} bv :
    SimplifyGoal (l ◁ₗ{β} bv @ bitfield R)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_place_bitfield l β R bv T).

  Lemma simplify_hyp_val_bitfield v R `{BitfieldDesc R} bv T :
    (v ◁ᵥ bitfield_repr bv @ bitfield_raw bitfield_it -∗ T)
    ⊢ simplify_hyp (v ◁ᵥ bv @ bitfield R) T.
  Proof. done. Qed.
  Global Instance simplify_hyp_val_bitfield_inst v R `{BitfieldDesc R} bv :
    SimplifyHypVal v (bv @ bitfield R)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_val_bitfield v R bv T).

  Lemma simplify_goal_val_bitfield v R `{BitfieldDesc R} bv T :
    T (v ◁ᵥ bitfield_repr bv @ bitfield_raw bitfield_it)
    ⊢ simplify_goal (v ◁ᵥ bv @ bitfield R) T.
  Proof.
    iIntros "HT". iExists _. iFrame. by iIntros "?".
  Qed.
  Global Instance simplify_goal_val_bitfield_inst v R `{BitfieldDesc R} bv :
    SimplifyGoalVal v (bv @ bitfield R)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_val_bitfield v R bv T).

End programs.
