From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional int singleton.
Set Default Proof Using "Type".

Section own.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition frac_ptr_type (β : own_state) (ty : type) (l' : loc) : type := {|
    ty_own β' l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β'] l' ∗ (l' ◁ₗ{own_state_min β' β} ty))%I;
  |}.
  Next Obligation.
    iIntros (β ?????) "($&Hl&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Global Instance frac_ptr_type_ne n : Proper ((=) ==> (dist n) ==> (=) ==> (dist n)) frac_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance frac_ptr_type_proper : Proper ((=) ==> (≡) ==> (=) ==> (≡)) frac_ptr_type.
  Proof. solve_type_proper. Qed.


  Program Definition frac_ptr (β : own_state) (ty : type) : rtype := {|
    rty_type := loc;
    rty := frac_ptr_type β ty
  |}.

  Global Program Instance rmovable_frac_ptr β ty : RMovable (frac_ptr β ty) := {|
    rmovable l := {|
      ty_layout := void*;
      ty_own_val v := (⌜v = val_of_loc l⌝ ∗ l ◁ₗ{β} ty)%I;
  |} |}.
  Next Obligation. iIntros (β ty l l'). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (β ty). by iDestruct 1 as (->) "_". Qed.
  Next Obligation. iIntros (β ty l l') "(%&Hl&Hl')". rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. iIntros (β ty l l' v ?) "Hl [-> Hl']". iFrame. iSplit => //. by rewrite left_id. Qed.
  Next Obligation. done. Qed.

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
    typed_place (DerefPCtx Na1Ord void* :: K) l β1 (p @ (frac_ptr β ty1)) T.
  Proof.
    iIntros "HP" (Φ) "(%&Hm&Hl) HΦ" => /=.
    iMod (heap_mapsto_own_state_to_mt with "Hm") as (q Hq) "Hm" => //.
    iApply (wp_deref with "Hm") => //; [naive_solver| by apply val_to_of_loc|].
    iIntros "!# Hm". iExists _. iSplit => //.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iFrame. iSplitR => //.
    by iApply heap_mapsto_own_state_from_mt.
  Qed.
  Global Instance type_place_frac_inst p β K β1 ty1 l :
    TypedPlace (DerefPCtx Na1Ord void* :: K) l β1 (p @ (frac_ptr β ty1)) :=
    λ T, i2p (type_place_frac _ _ _ _ _ _ _).

  Lemma type_addr_of (T : val → _) e:
    typed_addr_of e (λ l β ty, T l (t2mt (l @ frac_ptr β ty))) -∗
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

  (* Ideally we would like to have this version:
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
      (P -∗ loc_in_bounds l 0 ∗ True) ∧ (P -∗ T (val_of_loc l) (t2mt (l @ frac_ptr Own (place l))))) -∗
    typed_bin_op v1 (v1 ◁ᵥ offsetof s m) (l at{s}ₗ m) P (PtrNegOffsetOp ly) (IntOp size_t) PtrOp T.
  Proof.
    iDestruct 1 as (Hly) "HT". iIntros ([n [Ho Hi]]) "HP". iIntros (Φ) "HΦ".
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
    (T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) -∗
    typed_un_op p (p ◁ₗ{β} ty) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iApply wp_cast_loc. by apply val_to_of_loc.
    iApply ("HΦ" with "[Hp] HT") => //. by iFrame.
  Qed.
  Global Instance type_cast_ptr_ptr_inst (p : loc) β ty:
    TypedUnOp p (p ◁ₗ{β} ty)%I (CastOp PtrOp) PtrOp :=
    λ T, i2p (type_cast_ptr_ptr p β ty T).

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
    (⌜n ∈ it⌝ -∗ ∀ oid, T (val_of_loc (oid, n)) (t2mt ((oid, n) @ frac_ptr Own (place (oid, n))))) -∗
    typed_un_op v (v ◁ᵥ n @ int it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    iIntros "HT" (Hn Φ) "HΦ".
    move: (Hn). rewrite /val_to_Z_weak. move => /fmap_Some [i][Hi ->].
    iDestruct ("HT" with "[]") as "HT".
    { iPureIntro. by eapply val_to_int_repr_in_range. }
    iApply wp_cast_int_ptr => //. { by rewrite /val_to_loc_weak Hi. }
    rewrite /int_repr_to_loc /int_repr_to_Z. destruct i as [z|[id p]]=> /=.
    - iApply ("HΦ" with "[]"); last by iApply ("HT" $! None). done.
    - iApply ("HΦ" with "[]"); last by iApply ("HT" $! id). done.
  Qed.
  Global Instance type_cast_int_ptr_inst n v it:
    TypedUnOp v (v ◁ᵥ n @ int it)%I (CastOp PtrOp) (IntOp it) :=
    λ T, i2p (type_cast_int_ptr n v it T).

  Lemma type_copy_aid l1 β1 ty1 l2 β2 ty2 T:
    (l1 ◁ₗ{β1} ty1 -∗ l2 ◁ₗ{β2} ty2 -∗
      (loc_in_bounds (l2.1, l1.2) 0 ∗ True) ∧
      (alloc_alive_loc l2 ∗ True) ∧
      T (val_of_loc (l2.1, l1.2)) (t2mt (value void* (val_of_loc (l2.1, l1.2))))) -∗
    typed_copy_alloc_id l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) PtrOp T.
  Proof.
    iIntros "HT Hp1 Hp2" (Φ) "HΦ". iDestruct ("HT" with "Hp1 Hp2") as "HT".
    rewrite !right_id. iDestruct "HT" as "[#Hlib HT]".
    iApply wp_copy_alloc_id; [ by rewrite val_to_of_loc | by rewrite val_to_of_loc | done | ].
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]". by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_copy_aid_inst (l1 : loc) β1 ty1 (l2 : loc) β2 ty2:
    TypedCopyAllocId l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) PtrOp :=
    λ T, i2p (type_copy_aid l1 β1 ty1 l2 β2 ty2 T).

  (* TODO: Is it a good idea to have this general rule or would it be
  better to have more specialized rules? *)
  Lemma type_relop_ptr_ptr op b (l1 l2 : loc) β1 β2 ty1 ty2 T:
    match op with
    | LtOp => Some (bool_decide (l1.2 < l2.2))
    | GtOp => Some (bool_decide (l1.2 > l2.2))
    | LeOp => Some (bool_decide (l1.2 <= l2.2))
    | GeOp => Some (bool_decide (l1.2 >= l2.2))
    | _ => None
    end = Some b →
    (l1 ◁ₗ{β1} ty1 -∗ l2 ◁ₗ{β2} ty2 -∗ ⌜l1.1 = l2.1⌝ ∗ (
      (loc_in_bounds l1 0 ∗ True) ∧
      (loc_in_bounds l2 0 ∗ True) ∧
      (alloc_alive_loc l1 ∗ True) ∧
      T (i2v (Z_of_bool b) i32) (t2mt (b @ boolean i32)))) -∗
    typed_bin_op l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) op PtrOp PtrOp T.
  Proof.
    iIntros (?) "HT Hl1 Hl2". iIntros (Φ) "HΦ". iDestruct ("HT" with "Hl1 Hl2") as (Heq) "([#? _]&[#? _]&HT)".
    destruct op => //; simplify_eq.
    all: iApply wp_ptr_relop; try by [apply val_to_of_loc]; simpl; try done.
    all: try by case_bool_decide.
    all: iSplit; [ iDestruct "HT" as "[[$ _] _]" |].
    all: iSplit; [ iApply alloc_alive_loc_mono;[eassumption|]; iDestruct "HT" as "[[$ _] _]"| ].
    all: iModIntro; iDestruct "HT" as "[_ HT]".
    all: iApply "HΦ" => //; by case_bool_decide.
  Qed.
  Global Program Instance type_lt_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) LtOp PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr LtOp (bool_decide (l1.2 < l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_gt_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) GtOp PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr GtOp (bool_decide (l1.2 > l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_le_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) LeOp PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr LeOp (bool_decide (l1.2 <= l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
  Next Obligation. done. Qed.
  Global Program Instance type_ge_ptr_ptr_inst (l1 l2 : loc) β1 β2 ty1 ty2:
    TypedBinOp l1 (l1 ◁ₗ{β1} ty1) l2 (l2 ◁ₗ{β2} ty2) GeOp PtrOp PtrOp :=
    λ T, i2p (type_relop_ptr_ptr GeOp (bool_decide (l1.2 >= l2.2)) l1 l2 β1 β2 ty1 ty2 T _).
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
    iIntros (p ty E l ?) "(%&#Hmt&#Hty)".
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
    FindInContext (FindLoc l) 1%nat FICSyntactic :=
    λ T, i2p (find_in_context_type_loc_own l T).

  Lemma find_in_context_type_val_own l T:
    (∃ ty : type, l ◁ₗ ty ∗ T (t2mt (l @ frac_ptr Own ty))) -∗
    find_in_context (FindVal l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_type_val_own_inst (l : loc) :
    FindInContext (FindVal l) 1%nat FICSyntactic :=
    λ T, i2p (find_in_context_type_val_own l T).

  Lemma find_in_context_type_val_own_singleton (l : loc) T:
    (True ∗ T (t2mt (l @ frac_ptr Own (place l)))) -∗
    find_in_context (FindVal l) T.
  Proof. iIntros "[_ HT]". iExists _ => /=. iFrame "HT". simpl. done. Qed.
  Global Instance find_in_context_type_val_own_singleton_inst (l : loc):
    FindInContext (FindVal l) 2%nat FICSyntactic :=
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
    FindInContext (FindValP l) 2%nat FICSyntactic :=
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

  Program Definition ptr (n : nat) : rtype := {|
    rty_type := loc;
    rty l' := {|
      ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ loc_in_bounds l' n ∗ l ↦[β] l')%I;
  |} |}.
  Next Obligation. iIntros (????). iDestruct 1 as "[$ [$ ?]]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance rmovable_ptr n : RMovable (ptr n) := {|
    rmovable l := {|
      ty_layout := void*;
      ty_own_val v := (⌜v = val_of_loc l⌝ ∗ loc_in_bounds l n)%I;
  |} |}.
  Next Obligation. iIntros (l l'). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (n l v) "[Hv _]". by iDestruct "Hv" as %->. Qed.
  Next Obligation. iIntros (n l v) "[_ [? Hl]]". eauto with iFrame. Qed.
  Next Obligation. iIntros (n l l' v ?) "Hl [-> $]". by iFrame. Qed.
  Next Obligation. done. Qed.

  Instance ptr_loc_in_bounds l n β : LocInBounds (l @ ptr n) β bytes_per_addr.
  Proof.
    constructor. iIntros (?) "[_ [_ Hl]]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed.

  Lemma simplify_ptr_hyp_place (p:loc) l n T:
    (loc_in_bounds p n -∗ l ◁ₗ value void* (val_of_loc p) -∗ T) -∗
      simplify_hyp (l ◁ₗ p @ ptr n) T.
  Proof.
    iIntros "HT [% [#? Hl]]". iApply "HT"; first done. by repeat iSplit.
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
    iDestruct (ty_aligned with "Hp") as %?.
    iDestruct (ty_deref with "Hp") as (v) "[Hp [-> Hl]]".
    iDestruct ("HT" with "Hl") as "[#Hlib $]".
    iFrame "Hp Hlib". done.
  Qed.
  Global Instance subsume_own_ptr_inst p l1 l2 ty n:
    Subsume (p ◁ₗ l1 @ &own ty)%I (p ◁ₗ l2 @ ptr n)%I :=
    λ T, i2p (subsume_own_ptr p l1 l2 ty n T).

  Lemma type_copy_aid_ptr l1 β1 ty1 v2 l2 n T:
    (l1 ◁ₗ{β1} ty1 -∗ v2 ◁ᵥ l2 @ ptr n -∗
      ⌜l2.2 ≤ l1.2 ≤ l2.2 + n⌝ ∗
      ((alloc_alive_loc l2 ∗ True) ∧
      T (val_of_loc (l2.1, l1.2)) (t2mt (value void* (val_of_loc (l2.1, l1.2)))))) -∗
    typed_copy_alloc_id l1 (l1 ◁ₗ{β1} ty1) v2 (v2 ◁ᵥ l2 @ ptr n) PtrOp T.
  Proof.
    iIntros "HT Hp1 Hp2" (Φ) "HΦ". iDestruct "Hp2" as (->) "#Hlib".
    iDestruct ("HT" with "Hp1 [$Hlib]") as ([??]) "HT"; [done|].
    rewrite !right_id.
    iApply wp_copy_alloc_id; [ by rewrite val_to_of_loc | by rewrite val_to_of_loc |  | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done | done | etrans; [|done]; lia ]. }
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]". by iApply ("HΦ" with "[] HT").
  Qed.
  Global Instance type_copy_aid_ptr_inst (l1 : loc) β1 ty1 v2 (l2 : loc) n:
    TypedCopyAllocId l1 (l1 ◁ₗ{β1} ty1) v2 (v2 ◁ᵥ l2 @ ptr n)%I PtrOp :=
    λ T, i2p (type_copy_aid_ptr l1 β1 ty1 v2 l2 n T).
End ptr.

Section null.
  Context `{!typeG Σ}.
  Program Definition null : type := {|
    ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] NULL)%I;
  |}.
  Next Obligation. iIntros (???). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance movable_null : Movable null := {|
    ty_layout := void*;
    ty_own_val v := ⌜v = NULL⌝%I;
  |}.
  Next Obligation. by iIntros (?) "[% _]". Qed.
  Next Obligation. by iIntros (? ->). Qed.
  Next Obligation. iIntros (?) "[% ?]". iExists _. by iFrame. Qed.
  Next Obligation. iIntros (???) "? ->". by iFrame. Qed.

  Global Instance null_loc_in_bounds β : LocInBounds null β bytes_per_addr.
  Proof.
    constructor. iIntros (l) "[_ Hl]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    by iApply loc_in_bounds_shorten.
  Qed.

  Lemma type_null T :
    T (t2mt null) -∗
    typed_value NULL T.
  Proof. iIntros "HT". iExists  _. iFrame. done. Qed.
  Global Instance type_null_inst : TypedValue NULL := λ T, i2p (type_null T).

  Global Program Instance null_copyable : Copyable (null).
  Next Obligation.
    iIntros (E l ?) "[% Hl]".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    by iIntros "_".
  Qed.

  Lemma eval_bin_op_ptr_null (b : bool) op h (p : loc) v:
    heap_state_loc_in_bounds p 0 h.(st_heap) →
    (if b then op = NeOp else op = EqOp) →
    eval_bin_op op PtrOp PtrOp h p NULL v
     ↔ val_of_Z (Z_of_bool b) i32 = Some v.
  Proof.
    move => ??.
    destruct b => //; split => Heq; subst; try by [inversion Heq; simplify_eq].
    all: econstructor; rewrite ?val_to_of_loc /val_of_bool/i2v ?Heq //.
  Qed.

  Lemma eval_bin_op_null_null (b : bool) op h v:
    (if b then op = EqOp else op = NeOp) →
    eval_bin_op op PtrOp PtrOp h NULL NULL v
     ↔ val_of_Z (Z_of_bool b) i32 = Some v.
  Proof.
    move => ?.
    destruct b => //; split => Heq; subst; try by [inversion Heq; simplify_eq].
    all: by constructor => //; rewrite /i2v Heq.
  Qed.

  Lemma type_binop_null_null v1 v2 op T:
    (⌜match op with | EqOp | NeOp => True | _ => False end⌝ ∗ ∀ v,
          T v (t2mt ((if op is EqOp then true else false) @ boolean i32))) -∗
    typed_bin_op v1 (v1 ◁ᵥ null) v2 (v2 ◁ᵥ null) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT]" (-> -> Φ) "HΦ".
    iApply (wp_binop_det (i2v (Z_of_bool (if op is EqOp then true else false)) i32)). iSplit.
    { iIntros (??) "_ !%". destruct op => //; split => Heq; subst; try by [inversion Heq]; by constructor. }
    iApply "HΦ" => //. by destruct op.
  Qed.
  Global Instance type_binop_null_null_inst v1 v2 op:
    TypedBinOp v1 (v1 ◁ᵥ null) v2 (v2 ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_null_null v1 v2 op T).

  Lemma type_binop_ptr_null v2 op T (l : loc) ty β n `{!LocInBounds ty β n}:
    (⌜match op with | EqOp | NeOp => True | _ => False end⌝ ∗ ∀ v, l ◁ₗ{β} ty -∗
          T v (t2mt ((if op is EqOp then false else true) @ boolean i32))) -∗
    typed_bin_op l (l ◁ₗ{β} ty) v2 (v2 ◁ᵥ null) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT] Hl" (-> Φ) "HΦ".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#Hb".
    iDestruct (loc_in_bounds_shorten _ _ 0 with "Hb") as "#Hb0"; first by lia.
    iApply (wp_binop_det (i2v (Z_of_bool (if op is EqOp then false else true)) i32)). iSplit.
    { iIntros (??) "Hctx".
      iDestruct (loc_in_bounds_to_heap_loc_in_bounds with "Hb0 Hctx") as %?.
      iPureIntro. destruct op => //; split => Heq; subst; try by [inversion Heq].
      all: econstructor; rewrite ?val_to_of_loc /val_of_bool/i2v//. }
    iApply "HΦ". 2: by iApply "HT". by destruct op.
  Qed.
  Global Instance type_binop_ptr_null_inst v2 op (l : loc) ty β n `{!LocInBounds ty β n}:
    TypedBinOp l (l ◁ₗ{β} ty) v2 (v2 ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_ptr_null v2 op T l ty β n).

End null.

Section optionable.
  Context `{!typeG Σ}.

  Global Program Instance frac_ptr_optional ty β: ROptionable (frac_ptr β ty) null PtrOp PtrOp := {|
    ropt_opt p := {| opt_pre v1 v2 := (p ◁ₗ{β} ty -∗ loc_in_bounds p 0 ∗ True)%I |}
  |}.
  Next Obligation. move => ty ??. done. Qed.
  Next Obligation.
    iIntros (ty β p bty beq v1 v2 σ v) "Hpre H1 -> Hctx".
    destruct bty; [ iDestruct "H1" as (->) "Hty" | iDestruct "H1" as %-> ].
    - iDestruct (loc_in_bounds_to_heap_loc_in_bounds with "[Hpre Hty] Hctx") as %?;
        first by iDestruct ("Hpre" with "Hty") as "[$ _]".
      iPureIntro. by etrans; first apply (eval_bin_op_ptr_null (negb beq)); destruct beq => //.
    - iPureIntro. by etrans; first apply (eval_bin_op_null_null beq); destruct beq => //.
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

  Lemma subsume_optional_place_val_null ty l β T b ty' `{!Movable ty} `{!Optionable ty null ot1 ot2}:
    (⌜b⌝ ∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null) T.
  Proof. iIntros "[% Hsub] Hl". iDestruct ("Hsub" with "Hl") as "[Hl $]". iLeft. by iFrame. Qed.
  Global Instance subsume_optional_place_val_null_inst ty l β b ty' `{!Movable ty} `{!Optionable ty null ot1 ot2}:
    Subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null)%I | 20 :=
    λ T, i2p (subsume_optional_place_val_null ty l β T b ty').

  Lemma subsume_optionalO_place_val_null A (ty : A → type) l β T b ty' `{!∀ x, Movable (ty x)} `{!∀ x, Optionable (ty x) null ot1 ot2}:
    (⌜is_Some b⌝ ∗ ∀ x, ⌜b = Some x⌝ -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty x) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optionalO ty null) T.
  Proof. iDestruct 1 as ([x ->]) "Hsub". iIntros "Hl". by iApply "Hsub". Qed.
  Global Instance subsume_optionalO_place_val_null_inst A (ty : A → type) l β b ty' `{!∀ x, Movable (ty x)} `{!∀ x, Optionable (ty x) null ot1 ot2}:
    Subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optionalO ty null)%I | 20 :=
    λ T, i2p (subsume_optionalO_place_val_null A ty l β T b ty').
End optionable.

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
