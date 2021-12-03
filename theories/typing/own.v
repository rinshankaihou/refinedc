From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional boolean int singleton.
Set Default Proof Using "Type".

Section own.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition frac_ptr_type (β : own_state) (ty : type) (l' : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β' l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β'] l' ∗ (l' ◁ₗ{own_state_min β' β} ty))%I;
    ty_own_val v := (⌜v = val_of_loc l'⌝ ∗ l' ◁ₗ{β} ty)%I;
  |}.
  Next Obligation.
    iIntros (β ?????) "($&Hl&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (β ty l ot mt l' ->%is_ptr_ot_layout). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (β ty l ot mt v ->%is_ptr_ot_layout). by iDestruct 1 as (->) "_". Qed.
  Next Obligation. iIntros (β ty l ot mt l' ?) "(%&Hl&Hl')". rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. iIntros (β ty l ot mt l' v ->%is_ptr_ot_layout ?) "Hl [-> Hl']". iFrame. iSplit => //. by rewrite left_id. Qed.
  Next Obligation.
    iIntros (β ty l v ot mt st ?). apply: mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed.
  Global Instance frac_ptr_type_ne n : Proper ((=) ==> (dist n) ==> (=) ==> (dist n)) frac_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance frac_ptr_type_proper : Proper ((=) ==> (≡) ==> (=) ==> (≡)) frac_ptr_type.
  Proof. solve_type_proper. Qed.

  Definition frac_ptr (β : own_state) (ty : type) : rtype := RType (frac_ptr_type β ty).

  Global Instance frac_ptr_loc_in_bounds l ty β1 β2 : LocInBounds (l @ frac_ptr β1 ty) β2 bytes_per_addr.
  Proof.
    constructor. iIntros (?) "(_&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed.

  Lemma frac_ptr_mono ty1 ty2 l β β' p p' T:
    ⌜p = p'⌝ ∗ subsume (p ◁ₗ{own_state_min β β'} ty1) (p ◁ₗ{own_state_min β β'} ty2) T -∗
    subsume (l ◁ₗ{β} p @ frac_ptr β' ty1) (l ◁ₗ{β} p' @ frac_ptr β' ty2) T.
  Proof. iIntros "[-> Hsub] [$ [$ Hl]]". by iApply "Hsub". Qed.
  Global Instance frac_ptr_mono_inst ty1 ty2 l β β' p p':
    SubsumePlace l β (p @ frac_ptr β' ty1)%I (p' @ frac_ptr β' ty2)%I :=
    λ T, i2p (frac_ptr_mono ty1 ty2 l β β' p p' T).

  Global Instance frac_ptr_simple_mono ty1 ty2 p β P `{!SimpleSubsumePlace ty1 ty2 P}:
    SimpleSubsumePlaceR (frac_ptr β ty1) (frac_ptr β ty2) p p P.
  Proof. iIntros (l β') "HP [$ [$ Hl]]". iApply (@simple_subsume_place with "HP Hl"). Qed.

  Lemma type_place_frac p β K β1 ty1 T l:
    typed_place K p (own_state_min β1 β) ty1 (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, (p @ (frac_ptr β (typ t))))) -∗
    typed_place (DerefPCtx Na1Ord PtrOp :: K) l β1 (p @ (frac_ptr β ty1)) T.
  Proof.
    iIntros "HP" (Φ) "(%&Hm&Hl) HΦ" => /=.
    iMod (heap_mapsto_own_state_to_mt with "Hm") as (q Hq) "Hm" => //.
    iApply (wp_deref with "Hm") => //; [naive_solver| by apply val_to_of_loc|].
    iIntros "!# %st Hm". iExists _. rewrite mem_cast_id_loc. iSplit => //.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iFrame. iSplitR => //.
    by iApply heap_mapsto_own_state_from_mt.
  Qed.
  Global Instance type_place_frac_inst p β K β1 ty1 l :
    TypedPlace (DerefPCtx Na1Ord PtrOp :: K) l β1 (p @ (frac_ptr β ty1)) :=
    λ T, i2p (type_place_frac _ _ _ _ _ _ _).

  Lemma type_addr_of (T : val → _) e:
    typed_addr_of e (λ l β ty, T l (l @ frac_ptr β ty)) -∗
    typed_val_expr (& e) T.
  Proof.
    iIntros "Haddr" (Φ) "HΦ". rewrite /AddrOf.
    iApply "Haddr". iIntros (l β ty) "Hl HT".
    iApply ("HΦ" with "[Hl] HT").
    iSplit => //.
  Qed.

  Lemma simplify_frac_ptr (v : val) (p : loc) ty β T:
    (⌜v = p⌝ -∗ p ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp (v◁ᵥ p @ frac_ptr β ty) T.
  Proof. iIntros "HT Hl". iDestruct "Hl" as (->) "Hl". by iApply "HT". Qed.
  Global Instance simplify_frac_ptr_inst (v : val) (p : loc) ty β:
    SimplifyHypVal v (p @ frac_ptr β ty) (Some 0%N) :=
    λ T, i2p (simplify_frac_ptr v p ty β T).

  Lemma simplify_goal_frac_ptr_val ty (v : val) β (p : loc) T:
    T (⌜v = p⌝ ∗ p ◁ₗ{β} ty) -∗
      simplify_goal (v◁ᵥ p @ frac_ptr β ty) T.
  Proof.
    iIntros "HT". iExists _. iFrame.
    iIntros "[-> Hl]". iSplit => //.
  Qed.
  Global Instance simplify_goal_frac_ptr_val_inst ty v β p:
    SimplifyGoalVal v (p @ frac_ptr β ty) (Some 0%N) :=
    λ T, i2p (simplify_goal_frac_ptr_val ty v β p T).

  Lemma simplify_goal_frac_ptr_val_unrefined ty (v : val) β T:
    T (∃ p : loc, ⌜v = p⌝ ∗ p ◁ₗ{β} ty) -∗
      simplify_goal (v◁ᵥ frac_ptr β ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iDestruct 1 as (p) "[-> Hp]". iExists _. by iSplit. Qed.
  Global Instance simplify_goal_frac_ptr_val_unrefined_inst ty (v : val) β:
    SimplifyGoalVal v (frac_ptr β ty) (Some 0%N) :=
    λ T, i2p (simplify_goal_frac_ptr_val_unrefined ty v β T).

  Lemma simplify_frac_ptr_place_shr_to_own l p1 p2 β T:
    (⌜p1 = p2⌝ -∗ l ◁ₗ{β} p1 @ frac_ptr Own (place p2) -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} p1 @ frac_ptr Shr (place p2)) T.
  Proof. iIntros "HT (%&Hl&%)". subst. iApply "HT" => //. by iFrame. Qed.
  Global Instance simplify_frac_ptr_place_inst l p1 p2 β:
    SimplifyHypPlace l β (p1 @ frac_ptr Shr (place p2)) (Some 50%N) :=
    λ T, i2p (simplify_frac_ptr_place_shr_to_own l p1 p2 β T).

  (*
  TODO: revisit this comment
  Ideally we would like to have this version:
  Lemma own_val_to_own_place v l ty β T:
    val_to_loc v = Some l →
    l ◁ₗ{β} ty ∗ T -∗
    v ◁ᵥ l @ frac_ptr β ty ∗ T.
  Proof. by iIntros (->%val_of_to_loc) "[$ $]". Qed.
  But the sidecondition is a problem since solving it requires
  calling apply which triggers https://github.com/coq/coq/issues/6583
  and can make the application of this lemma fail if it tries to solve
  a Movable (tc_opaque x) in the context. *)

  Lemma own_val_to_own_place (l : loc) ty β T:
    l ◁ₗ{β} ty ∗ T -∗
    l ◁ᵥ l @ frac_ptr β ty ∗ T.
  Proof. by iIntros "[$ $]". Qed.

  Lemma own_val_to_own_place_singleton (l : loc) β T:
    T -∗
    l ◁ᵥ l @ frac_ptr β (place l) ∗ T.
  Proof. by iIntros "$". Qed.


  Global Instance strip_guarded_frac_ptr_refined p β β' E1 E2 ty ty' `{!StripGuarded (own_state_min β β') E1 E2 ty ty'}:
    StripGuarded β E1 E2 (p @ frac_ptr β' ty) (p @ frac_ptr β' ty').
  Proof.
    iIntros (l E HE1 HE2) "Hs". iDestruct "Hs" as "($&$&Hty)".
    by iDestruct (strip_guarded with "Hty") as "Hty".
  Qed.

  (* TODO: find the right instance for ty_of_rty such that this instance is not necessary anymore *)
  Global Instance strip_guarded_frac_ptr β β' E1 E2 ty ty' `{!StripGuarded (own_state_min β β') E1 E2 ty ty'}:
    StripGuarded β E1 E2 (frac_ptr β' ty) (frac_ptr β' ty').
  Proof.
    iIntros (l E HE1 HE2) "Hs". iDestruct "Hs" as (p) "($&Hl&Hty)". iExists _. iFrame.
    by iDestruct (strip_guarded with "Hty") as "Hty".
  Qed.

  Lemma type_offset_of_sub v1 l s m P ly T:
    ⌜ly_size ly = 1%nat⌝ ∗ (
      (P -∗ loc_in_bounds l 0 ∗ True) ∧ (P -∗ T (val_of_loc l) (l @ frac_ptr Own (place l)))) -∗
    typed_bin_op v1 (v1 ◁ᵥ offsetof s m) (l at{s}ₗ m) P (PtrNegOffsetOp ly) (IntOp size_t) PtrOp T.
  Proof.
    iDestruct 1 as (Hly) "HT". unfold offsetof, int, int_inner_type; simpl_type.
    iIntros ([n [Ho Hi]]) "HP". iIntros (Φ) "HΦ".
    iAssert (loc_in_bounds l 0) as "#Hlib".
    { iDestruct "HT" as "[HT _]". by iDestruct ("HT" with "HP") as "[$ _]". }
    iDestruct "HT" as "[_ HT]".
    iApply wp_ptr_neg_offset. by apply val_to_of_loc. done.
    all: rewrite offset_loc_sz1 // /GetMemberLoc shift_loc_assoc Ho /= Z.add_opp_diag_r shift_loc_0.
    1: done.
    iModIntro. iApply "HΦ"; [ | by iApply "HT"]. done.
  Qed.
  Global Instance type_offset_of_sub_inst v1 l s m P ly:
    TypedBinOp v1 (v1 ◁ᵥ offsetof s m) (l at{s}ₗ m) P (PtrNegOffsetOp ly) (IntOp size_t) PtrOp :=
    λ T, i2p (type_offset_of_sub v1 l s m P ly T).

  Lemma type_cast_ptr_ptr p β ty T:
    (T (val_of_loc p) (p @ frac_ptr β ty)) -∗
    typed_un_op p (p ◁ₗ{β} ty) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iApply wp_cast_loc; [by apply val_to_of_loc|].
    iApply ("HΦ" with "[Hp] HT") => //. by iFrame.
  Qed.
  Global Instance type_cast_ptr_ptr_inst (p : loc) β ty:
    TypedUnOp p (p ◁ₗ{β} ty)%I (CastOp PtrOp) PtrOp :=
    λ T, i2p (type_cast_ptr_ptr p β ty T).

  Lemma type_if_ptr_own l β ty T1 T2:
    (l ◁ₗ{β} ty -∗ (loc_in_bounds l 0 ∗ True) ∧ T1) -∗
    typed_if PtrOp l (l ◁ₗ{β} ty) T1 T2.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "[[#Hlib _] HT]".
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[? H].
    iExists l. iSplit; first by rewrite val_to_of_loc.
    iSplitR. { by iApply wp_if_precond_alloc. }
    by rewrite bool_decide_true; last by move: l H => [??] /= -> //.
  Qed.
  Global Instance type_if_ptr_own_inst (l : loc) β ty:
    TypedIf PtrOp l (l ◁ₗ{β} ty)%I :=
    λ T1 T2, i2p (type_if_ptr_own l β ty T1 T2).

  Lemma type_assert_ptr_own l β ty s fn ls R Q:
    (l ◁ₗ{β} ty -∗ (loc_in_bounds l 0 ∗ True) ∧ typed_stmt s fn ls R Q) -∗
    typed_assert PtrOp l (l ◁ₗ{β} ty) s fn ls R Q.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "[[#Hlib _] HT]".
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[? H].
    iExists l. iSplit; first by rewrite val_to_of_loc.
    iSplit. { iPureIntro. move: l H => [??] /= -> //. }
    iSplitR. { by iApply wp_if_precond_alloc. }
    by iApply "HT".
  Qed.
  Global Instance type_assert_ptr_own_inst (l : loc) β ty:
    TypedAssert PtrOp l (l ◁ₗ{β} ty)%I :=
    λ s fn ls R Q, i2p (type_assert_ptr_own l β ty s fn ls R Q).

  Lemma type_place_cast_ptr_ptr K l ty β T:
    typed_place K l β ty T -∗
    typed_place (UnOpPCtx (CastOp PtrOp) :: K) l β ty T.
  Proof.
    iIntros "HP" (Φ) "Hl HΦ" => /=.
    iApply wp_cast_loc. { by apply val_to_of_loc. }
    iIntros "!#". iExists _. iSplit => //.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". by iFrame.
  Qed.
  Global Instance type_place_cast_ptr_ptr_inst K l ty β:
    TypedPlace (UnOpPCtx (CastOp PtrOp) :: K) l β ty :=
    λ T, i2p (type_place_cast_ptr_ptr K l ty β T).

  Lemma type_cast_int_ptr n v it T:
    (⌜n ∈ it⌝ -∗ ∀ oid, T (val_of_loc (oid, n)) ((oid, n) @ frac_ptr Own (place (oid, n)))) -∗
    typed_un_op v (v ◁ᵥ n @ int it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hn Φ) "HΦ".
    iDestruct ("HT" with "[%]") as "HT".
    { by apply: val_to_Z_in_range. }
    iApply wp_cast_int_ptr_weak => //.
    iIntros (i') "!>". by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_cast_int_ptr_inst n v it:
    TypedUnOp v (v ◁ᵥ n @ int it)%I (CastOp PtrOp) (IntOp it) | 50 :=
    λ T, i2p (type_cast_int_ptr n v it T).

  Lemma type_copy_aid v a it l β ty T:
    (
      l ◁ₗ{β} ty -∗
      (loc_in_bounds (l.1, a) 0 ∗ True) ∧
      (alloc_alive_loc l ∗ True) ∧
      T (val_of_loc (l.1, a)) ((l.1, a) @ frac_ptr Own (place (l.1, a)))
    ) -∗
    typed_copy_alloc_id v (v ◁ᵥ a @ int it) l (l ◁ₗ{β} ty) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT %Hv Hl" (Φ) "HΦ". iDestruct ("HT" with "Hl") as "HT".
    rewrite !right_id. iDestruct "HT" as "[#Hlib HT]".
    iApply wp_copy_alloc_id; [ done | by rewrite val_to_of_loc | done | ].
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]".
    by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_copy_aid_inst (v : val) a it (l : loc) β ty:
    TypedCopyAllocId v (v ◁ᵥ a @ int it)%I l (l ◁ₗ{β} ty) (IntOp it) :=
    λ T, i2p (type_copy_aid v a it l β ty T).

  (* TODO: Is it a good idea to have this general rule or would it be
  better to have more specialized rules? *)
  Lemma type_relop_ptr_ptr op b (l1 l2 : loc) β1 β2 ty1 ty2 T:
    match op with
    | LtOp rit => Some (bool_decide (l1.2 < l2.2), rit)
    | GtOp rit => Some (bool_decide (l1.2 > l2.2), rit)
    | LeOp rit => Some (bool_decide (l1.2 <= l2.2), rit)
    | GeOp rit => Some (bool_decide (l1.2 >= l2.2), rit)
    | _ => None
    end = Some (b, i32) →
    (l1 ◁ₗ{β1} ty1 -∗ l2 ◁ₗ{β2} ty2 -∗ ⌜l1.1 = l2.1⌝ ∗ (
      (loc_in_bounds l1 0 ∗ True) ∧
      (loc_in_bounds l2 0 ∗ True) ∧
      (alloc_alive_loc l1 ∗ True) ∧
      T (i2v (bool_to_Z b) i32) (b @ boolean i32))) -∗
    typed_bin_op l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) op PtrOp PtrOp T.
  Proof.
    iIntros (?) "HT Hl1 Hl2". iIntros (Φ) "HΦ". iDestruct ("HT" with "Hl1 Hl2") as (Heq) "([#? _]&[#? _]&HT)".
    have [v' Hv'] := val_of_Z_bool_is_Some None i32 b.
    rewrite /i2v Hv' /=.
    destruct op => //; simplify_eq.
    all: iApply wp_ptr_relop; [by apply val_to_of_loc|by apply val_to_of_loc|done|simpl|done|done|].
    all: try by rewrite bool_decide_true.
    all: iSplit; [ iDestruct "HT" as "[[$ _] _]" |].
    all: iSplit; [ iApply alloc_alive_loc_mono;[eassumption|]; iDestruct "HT" as "[[$ _] _]"| ].
    all: iModIntro; iDestruct "HT" as "[_ HT]".
    all: iApply ("HΦ" with "[] HT") => //.
    all: iExists _; iSplit; iPureIntro; [apply: val_to_of_Z | done].
    all: done.
  Qed.
  Global Program Instance type_lt_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) (LtOp i32) PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr (LtOp i32) (bool_decide (l1.2 < l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_gt_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) (GtOp i32) PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr (GtOp i32) (bool_decide (l1.2 > l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_le_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) (LeOp i32) PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr (LeOp i32) (bool_decide (l1.2 <= l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_ge_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) (GeOp i32) PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr (GeOp i32) (bool_decide (l1.2 >= l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.


  (* Lemma type_roundup_frac_ptr v2 β ty P2 T p: *)
  (*   (P2 -∗ T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) -∗ *)
  (*     typed_bin_op p (p ◁ₗ{β} ty) v2 P2 RoundUpOp T. *)
  (* Proof. *)
  (*   iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ". *)
  (*   iApply wp_binop_det. by move => h /=; rewrite val_to_of_loc. *)
  (*   iApply ("HΦ" with "[Hv1]"); last by iApply "HT". *)
  (*   by iFrame. *)
  (* Qed. *)
  (* Global Instance type_roundup_frac_ptr_inst v2 β ty P2 T (p : loc) : *)
  (*   TypedBinOp p (p ◁ₗ{β} ty) v2 P2 RoundUpOp T := *)
  (*   i2p (type_roundup_frac_ptr v2 β ty P2 T p). *)

  (* Lemma type_rounddown_frac_ptr v2 β ty P2 T p: *)
  (*   (P2 -∗ T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) -∗ *)
  (*     typed_bin_op p (p ◁ₗ{β} ty) v2 P2 RoundDownOp T. *)
  (* Proof. *)
  (*   iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ". *)
  (*   iApply wp_binop_det. by move => h /=; rewrite val_to_of_loc. *)
  (*   iApply ("HΦ" with "[Hv1]"); last by iApply "HT". *)
  (*   by iFrame. *)
  (* Qed. *)
  (* Global Instance type_rounddown_frac_ptr_inst v2 β ty P2 T (p : loc) : *)
  (*   TypedBinOp p (p ◁ₗ{β} ty) v2 P2 RoundDownOp T := *)
  (*   i2p (type_rounddown_frac_ptr v2 β ty P2 T p). *)

  Global Program Instance shr_copyable p ty : Copyable (p @ frac_ptr Shr ty).
  Next Obligation.
    iIntros (p ty E ot l ? ->%is_ptr_ot_layout) "(%&#Hmt&#Hty)".
    iMod (heap_mapsto_own_state_to_mt with "Hmt") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //. by iSplit.
    by iIntros "_".
  Qed.

  Lemma find_in_context_type_loc_own l T:
    (∃ l1 β1 β ty, l1 ◁ₗ{β1} (l @ frac_ptr β ty) ∗ (l1 ◁ₗ{β1} (l @ frac_ptr β (place l)) -∗
      T (own_state_min β1 β, ty))) -∗
    find_in_context (FindLoc l) T.
  Proof.
    iDestruct 1 as (l1 β1 β ty) "[[% [Hmt Hl]] HT]".
    iExists (_, _) => /=. iFrame. iApply "HT".
    iSplit => //. by iFrame.
  Qed.
  Global Instance find_in_context_type_loc_own_inst l :
    FindInContext (FindLoc l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_type_loc_own l T).

  Lemma find_in_context_type_val_own l T:
    (∃ ty : type, l ◁ₗ ty ∗ T (l @ frac_ptr Own ty)) -∗
    find_in_context (FindVal l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_type_val_own_inst (l : loc) :
    FindInContext (FindVal l) FICSyntactic | 10 :=
    λ T, i2p (find_in_context_type_val_own l T).

  Lemma find_in_context_type_val_own_singleton (l : loc) T:
    (True ∗ T (l @ frac_ptr Own (place l))) -∗
    find_in_context (FindVal l) T.
  Proof. iIntros "[_ HT]". iExists _ => /=. iFrame "HT". simpl. done. Qed.
  Global Instance find_in_context_type_val_own_singleton_inst (l : loc):
    FindInContext (FindVal l) FICSyntactic | 20 :=
    λ T, i2p (find_in_context_type_val_own_singleton l T).

  (* We cannot use place here as it can easily lead to an infinite
  loop during type checking. Thus, we define place' that is not
  unfolded as eagerly as place. You probably should not add typing
  rules for place', but for place instead. *)
  Definition place' (l : loc) : type := place l.
  Lemma find_in_context_type_val_P_own_singleton (l : loc) T:
    (True ∗ T (l ◁ₗ place' l)) -∗
    find_in_context (FindValP l) T.
  Proof. rewrite /place'. iIntros "[_ HT]". iExists _. iFrame "HT" => //=. Qed.
  Global Instance find_in_context_type_val_P_own_singleton_inst (l : loc):
    FindInContext (FindValP l) FICSyntactic | 30 :=
    λ T, i2p (find_in_context_type_val_P_own_singleton l T).
End own.
Typeclasses Opaque place'.
Notation "place'< l >" := (place' l) (only printing, format "'place'<' l '>'") : printing_sugar.

Notation "&frac{ β }" := (frac_ptr β) (format "&frac{ β }") : bi_scope.
Notation "&own" := (frac_ptr Own) (format "&own") : bi_scope.
Notation "&shr" := (frac_ptr Shr) (format "&shr") : bi_scope.

Notation "&frac< β , ty >" := (frac_ptr β ty) (only printing, format "'&frac<' β ,  ty '>'") : printing_sugar.
Notation "&own< ty >" := (frac_ptr Own ty) (only printing, format "'&own<' ty '>'") : printing_sugar.
Notation "&shr< ty >" := (frac_ptr Shr ty) (only printing, format "'&shr<' ty '>'") : printing_sugar.

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr_type (n : nat) (l' : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l' n ∗ l ↦[β] l')%I;
    ty_own_val v := (⌜v = val_of_loc l'⌝ ∗ loc_in_bounds l' n)%I;
  |}.
  Next Obligation. iIntros (????). iDestruct 1 as "[$ [$ ?]]". by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (n l ot mt l' ->%is_ptr_ot_layout). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (n l ot mt v ->%is_ptr_ot_layout) "[Hv _]". by iDestruct "Hv" as %->. Qed.
  Next Obligation. iIntros (n l ot mt v ?) "[_ [? Hl]]". eauto with iFrame. Qed.
  Next Obligation. iIntros (n l ot mt l' v ->%is_ptr_ot_layout ?) "Hl [-> $]". by iFrame. Qed.
  Next Obligation.
    iIntros (n l v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed.

  Definition ptr (n : nat) : rtype := RType (ptr_type n).

  Instance ptr_loc_in_bounds l n β : LocInBounds (l @ ptr n) β bytes_per_addr.
  Proof.
    constructor. iIntros (?) "[_ [_ Hl]]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed.

  Lemma simplify_ptr_hyp_place (p:loc) l n T:
    (loc_in_bounds p n -∗ l ◁ₗ value PtrOp (val_of_loc p) -∗ T) -∗
      simplify_hyp (l ◁ₗ p @ ptr n) T.
  Proof.
    iIntros "HT [% [#? Hl]]". iApply "HT"; first done.
    repeat iSplit => //. iPureIntro. by apply: mem_cast_id_loc.
  Qed.
  Global Instance simplify_ptr_hyp_place_inst p l n:
    SimplifyHypPlace l Own (p @ ptr n)%I (Some 0%N) :=
    λ T, i2p (simplify_ptr_hyp_place p l n T).

  Lemma simplify_ptr_goal_val (p:loc) l n T:
    T (⌜l = p⌝ ∗ loc_in_bounds l n) -∗ simplify_goal (p ◁ᵥ l @ ptr n) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[-> ?]". by iFrame. Qed.
  Global Instance simplify_ptr_goal_val_inst (p : loc) l n:
    SimplifyGoalVal p (l @ ptr n)%I (Some 10%N) :=
    λ T, i2p (simplify_ptr_goal_val p l n T).

  Lemma subsume_own_ptr p l1 l2 ty n T:
    ⌜l1 = l2⌝ ∗ (l1 ◁ₗ ty -∗ loc_in_bounds l1 n ∗ T) -∗
    subsume (p ◁ₗ l1 @ &own ty)%I (p ◁ₗ l2 @ ptr n)%I T.
  Proof.
    iIntros "[-> HT] Hp".
    iDestruct (ty_aligned _ PtrOp MCNone with "Hp") as %?; [done|].
    iDestruct (ty_deref _ PtrOp MCNone with "Hp") as (v) "[Hp [-> Hl]]"; [done|].
    iDestruct ("HT" with "Hl") as "[#Hlib $]".
    iFrame "Hp Hlib". done.
  Qed.
  Global Instance subsume_own_ptr_inst p l1 l2 ty n:
    Subsume (p ◁ₗ l1 @ &own ty)%I (p ◁ₗ l2 @ ptr n)%I :=
    λ T, i2p (subsume_own_ptr p l1 l2 ty n T).

  Lemma type_copy_aid_ptr v1 a it v2 l n T:
    (
      v1 ◁ᵥ a @ int it -∗
      v2 ◁ᵥ l @ ptr n -∗
      ⌜l.2 ≤ a ≤ l.2 + n⌝ ∗
      (alloc_alive_loc l ∗ True) ∧
      T (val_of_loc (l.1, a)) (value PtrOp (val_of_loc (l.1, a)))
    ) -∗
    typed_copy_alloc_id v1 (v1 ◁ᵥ a @ int it) v2 (v2 ◁ᵥ l @ ptr n) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT %Hv1 Hv2" (Φ) "HΦ". iDestruct "Hv2" as "[-> #Hlib]".
    iDestruct ("HT" with "[//] [$Hlib]") as ([??]) "HT"; [done|].
    rewrite !right_id.
    iApply wp_copy_alloc_id; [ done | by rewrite val_to_of_loc |  | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done | done | etrans; [|done]; lia ]. }
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]". iApply ("HΦ" with "[] HT").
    iSplit => //. iPureIntro. apply: mem_cast_id_loc.
  Qed.
  Global Instance type_copy_aid_ptr_inst v1 a it v2 (l : loc) n:
    TypedCopyAllocId v1 (v1 ◁ᵥ a @ int it)%I v2 (v2 ◁ᵥ l @ ptr n)%I (IntOp it) :=
    λ T, i2p (type_copy_aid_ptr v1 a it v2 l n T).
End ptr.

Section null.
  Context `{!typeG Σ}.
  Program Definition null : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] NULL)%I;
    ty_own_val v := ⌜v = NULL⌝%I;
  |}.
  Next Obligation. iIntros (???). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. by iIntros (???->%is_ptr_ot_layout) "[% _]". Qed.
  Next Obligation. by iIntros (???->%is_ptr_ot_layout->). Qed.
  Next Obligation. iIntros (????) "[% ?]". iExists _. by iFrame. Qed.
  Next Obligation. iIntros (????->%is_ptr_ot_layout?) "? ->". by iFrame. Qed.
  Next Obligation. iIntros (v ot mt st ?). apply mem_cast_compat_loc; [done|]. iPureIntro. naive_solver. Qed.

  Global Instance null_loc_in_bounds β : LocInBounds null β bytes_per_addr.
  Proof.
    constructor. iIntros (l) "[_ Hl]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    by iApply loc_in_bounds_shorten.
  Qed.

  Lemma type_null T :
    T null -∗
    typed_value NULL T.
  Proof. iIntros "HT". iExists  _. iFrame. done. Qed.
  Global Instance type_null_inst : TypedValue NULL := λ T, i2p (type_null T).

  Global Program Instance null_copyable : Copyable (null).
  Next Obligation.
    iIntros (E l ??->%is_ptr_ot_layout) "[% Hl]".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    by iIntros "_".
  Qed.

  Lemma eval_bin_op_ptr_cmp l1 l2 op h v b it:
    match op with | EqOp it' | NeOp it' => it' = it | _ =>  False end →
    heap_loc_eq l1 l2 h.(st_heap) = Some b →
    eval_bin_op op PtrOp PtrOp h l1 l2 v
     ↔ val_of_Z (bool_to_Z (if op is EqOp _ then b else negb b)) it None = Some v.
  Proof.
    move => ??. split.
    - inversion 1; rewrite ->?val_to_of_loc in *; simplify_eq/= => //; destruct op => //; simplify_eq; done.
    - move => ?. apply: CmpOpPP; rewrite ?val_to_of_loc //. destruct op => //; simplify_eq; done.
  Qed.

  Lemma type_binop_null_null v1 v2 op T:
    (⌜match op with | EqOp rit | NeOp rit => rit = i32 | _ => False end⌝ ∗ ∀ v,
          T v ((if op is EqOp i32 then true else false) @ boolean i32)) -∗
    typed_bin_op v1 (v1 ◁ᵥ null) v2 (v2 ◁ᵥ null) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT]" (-> -> Φ) "HΦ".
    have Hz:= val_of_Z_bool (if op is EqOp i32 then true else false) i32.
    iApply (wp_binop_det_pure (i2v (bool_to_Z (if op is EqOp i32 then true else false)) i32)). {
      move => ??. rewrite eval_bin_op_ptr_cmp // ?heap_loc_eq_NULL_NULL //= Hz. naive_solver.
    }
    iApply "HΦ" => //. iExists _. iSplit; iPureIntro => //. by destruct op.
  Qed.
  Global Instance type_binop_null_null_inst v1 v2 op:
    TypedBinOp v1 (v1 ◁ᵥ null) v2 (v2 ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_null_null v1 v2 op T).

  Lemma type_binop_ptr_null v op (l : loc) ty β n `{!LocInBounds ty β n} T:
    (⌜match op with EqOp rit | NeOp rit => rit = i32 | _ => False end⌝ ∗ ∀ v, l ◁ₗ{β} ty -∗
          T v ((if op is EqOp _ then false else true) @ boolean i32)) -∗
    typed_bin_op l (l ◁ₗ{β} ty) v (v ◁ᵥ null) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT] Hl" (-> Φ) "HΦ".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#Hb".
    iDestruct (loc_in_bounds_shorten _ _ 0 with "Hb") as "#Hb0"; first by lia.
    have Hz:= val_of_Z_bool (if op is EqOp i32 then false else true) i32.
    iApply (wp_binop_det (i2v (bool_to_Z (if op is EqOp i32 then false else true)) i32)).
    iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
    iDestruct (loc_in_bounds_has_alloc_id with "Hb") as %[??].
    iDestruct (wp_if_precond_heap_loc_eq with "[] Hctx") as %?. { by iApply wp_if_precond_alloc. }
    iSplit.
    { iPureIntro => ?. rewrite eval_bin_op_ptr_cmp //. case_bool_decide => //; simplify_eq. naive_solver. }
    iModIntro. iMod "HE". iModIntro. iFrame.
    iApply "HΦ". 2: by iApply "HT". iExists _. iSplit; iPureIntro => //. by destruct op.
  Qed.
  Global Instance type_binop_ptr_null_inst v op (l : loc) ty β n `{!LocInBounds ty β n}:
    TypedBinOp l (l ◁ₗ{β} ty) v (v ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_ptr_null v op l ty β n T).

  Lemma type_binop_null_ptr v op (l : loc) ty β n `{!LocInBounds ty β n} T:
    (⌜match op with EqOp rit | NeOp rit => rit = i32 | _ => False end⌝ ∗ ∀ v, l ◁ₗ{β} ty -∗
          T v (((if op is EqOp _ then false else true) @ boolean i32))) -∗
    typed_bin_op v (v ◁ᵥ null) l (l ◁ₗ{β} ty) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT] -> Hl %Φ HΦ".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#Hb".
    iDestruct (loc_in_bounds_shorten _ _ 0 with "Hb") as "#Hb0"; first by lia.
    have ?:= val_of_Z_bool (if op is EqOp _ then false else true) i32.
    iApply (wp_binop_det (i2v (bool_to_Z (if op is EqOp _ then false else true)) i32)).
    iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
    iDestruct (loc_in_bounds_has_alloc_id with "Hb") as %[??].
    iDestruct (wp_if_precond_heap_loc_eq with "[] Hctx") as %Heq. { by iApply wp_if_precond_alloc. }
    rewrite heap_loc_eq_symmetric in Heq.
    iSplit.
    { iPureIntro => ?. rewrite eval_bin_op_ptr_cmp //. case_bool_decide => //; simplify_eq. naive_solver. }
    iModIntro. iMod "HE". iModIntro. iFrame.
    iApply "HΦ". 2: by iApply "HT". iExists _. iSplit; iPureIntro => //; by destruct op.
  Qed.
  Global Instance type_binop_null_ptr_inst v op (l : loc) ty β n `{!LocInBounds ty β n}:
    TypedBinOp v (v ◁ᵥ null) l (l ◁ₗ{β} ty) op PtrOp PtrOp :=
    λ T, i2p (type_binop_null_ptr v op l ty β n T).

  Lemma type_cast_null_int it v T:
    (T (i2v 0 it) (0 @ int it)) -∗
    typed_un_op v (v ◁ᵥ null) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "HT" (-> Φ) "HΦ".
    iApply wp_cast_null_int.
    { by apply: (val_of_Z_bool false). }
    iModIntro. iApply ("HΦ" with "[] HT").
    unfold int; simpl_type. iPureIntro. apply: (i2v_bool_Some false).
  Qed.
  Global Instance type_cast_null_int_inst v it:
    TypedUnOpVal v null (CastOp (IntOp it)) PtrOp :=
    λ T, i2p (type_cast_null_int it v T).

  Lemma type_cast_zero_ptr v it T:
    (T (val_of_loc NULL_loc) null) -∗
    typed_un_op v (v ◁ᵥ 0 @ int it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hv Φ) "HΦ".
    iApply wp_cast_int_null; first done.
    iModIntro. by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_cast_zero_ptr_inst v it:
    TypedUnOpVal v (0 @ int it) (CastOp PtrOp) (IntOp it) | 10 :=
    λ T, i2p (type_cast_zero_ptr v it T).

  Lemma type_if_null v T1 T2:
    T2 -∗
    typed_if PtrOp v (v ◁ᵥ null) T1 T2.
  Proof.
    iIntros "HT2 ->". iExists NULL_loc.
    rewrite val_to_of_loc bool_decide_false; last naive_solver. iFrame.
    iSplit; [done|]. by iApply wp_if_precond_null.
  Qed.
  Global Instance type_if_null_inst v:
    TypedIf PtrOp v (v ◁ᵥ null)%I :=
    λ T1 T2, i2p (type_if_null v T1 T2).
End null.

Section optionable.
  Context `{!typeG Σ}.

  Global Program Instance frac_ptr_optional ty β: ROptionable (frac_ptr β ty) null PtrOp PtrOp := {|
    ropt_opt p := {| opt_pre v1 v2 := (p ◁ₗ{β} ty -∗ loc_in_bounds p 0 ∗ True)%I |}
  |}.
  Next Obligation.
    iIntros (ty β p bty beq v1 v2 σ v) "Hpre H1 -> Hctx".
    destruct bty; [ iDestruct "H1" as (->) "Hty" | iDestruct "H1" as %-> ].
    - iDestruct ("Hpre" with "Hty") as "[#Hlib _]".
      iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[??].
      iDestruct (wp_if_precond_heap_loc_eq with "[] Hctx") as %Heq. { by iApply wp_if_precond_alloc. }
      iPureIntro. rewrite eval_bin_op_ptr_cmp //; destruct beq => //; case_bool_decide; naive_solver.
    - iPureIntro. rewrite eval_bin_op_ptr_cmp // ?heap_loc_eq_NULL_NULL //; destruct beq => //; case_bool_decide; naive_solver.
  Qed.
  Global Program Instance frac_ptr_optional_agree ty1 ty2 β : OptionableAgree (frac_ptr β ty1) (frac_ptr β ty2).
  Next Obligation. done. Qed.


  (* Global Program Instance ptr_optional : ROptionable ptr null PtrOp PtrOp := {| *)
  (*   ropt_opt x := {| opt_alt_sz := _ |} *)
  (* |}. *)
  (* Next Obligation. move => ?. done. Qed. *)
  (* Next Obligation. *)
  (*   iIntros (p bty beq v1 v2 σ v) "H1 -> Hctx". *)
  (*   destruct bty; [ iDestruct "H1" as %-> | iDestruct "H1" as %-> ]; iPureIntro. *)
  (*   - admit. (*by etrans; first apply (eval_bin_op_ptr_null (negb beq)); destruct beq => //.*) *)
  (*   - by etrans; first apply (eval_bin_op_null_null beq); destruct beq => //. *)
  (* Admitted. *)

  Lemma subsume_optional_place_val_null ty l β T b ty' `{!Optionable ty null ot1 ot2}:
    (⌜b⌝ ∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null) T.
  Proof. iIntros "[% Hsub] Hl". unfold optional; simpl_type. iDestruct ("Hsub" with "Hl") as "[Hl $]". iLeft. by iFrame. Qed.
  Global Instance subsume_optional_place_val_null_inst ty l β b ty' `{!Optionable ty null ot1 ot2}:
    Subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null)%I | 20 :=
    λ T, i2p (subsume_optional_place_val_null ty l β T b ty').

  Lemma subsume_optionalO_place_val_null A (ty : A → type) l β T b ty' `{!∀ x, Optionable (ty x) null ot1 ot2}:
    (⌜is_Some b⌝ ∗ ∀ x, ⌜b = Some x⌝ -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty x) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optionalO ty null) T.
  Proof. iDestruct 1 as ([x ->]) "Hsub". unfold optionalO; simpl_type. iIntros "Hl". by iApply "Hsub". Qed.
  Global Instance subsume_optionalO_place_val_null_inst A (ty : A → type) l β b ty' `{!∀ x, Optionable (ty x) null ot1 ot2}:
    Subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optionalO ty null)%I | 20 :=
    λ T, i2p (subsume_optionalO_place_val_null A ty l β T b ty').
End optionable.

Typeclasses Opaque ptr_type.
Typeclasses Opaque frac_ptr_type.

Section optional_null.
  Context `{!typeG Σ}.

  Typeclasses Transparent optional_type.

  Lemma type_place_optional_null K l β1 b ty T:
    ⌜b⌝ ∗ typed_place K l β1 ty T -∗
    typed_place K l β1 (b @ optional ty null) T.
  Proof.
    iIntros "[% H]" (Φ) "[[_ Hl]|[% _]] HH"; last done.
    by iApply ("H" with "Hl").
  Qed.

  (* This should have a lower priority than type_place_id *)
  Global Instance type_place_optional_null_inst K l β1 b ty :
    TypedPlace K l β1 (b @ optional ty null) | 100 :=
    λ T, i2p (type_place_optional_null K l β1 b ty T).
End optional_null.
