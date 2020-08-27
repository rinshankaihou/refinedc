From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional int singleton.
Set Default Proof Using "Type".

Section own.
  Context `{!typeG Σ}.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition frac_ptr_type (β : own_state) (ty : type) (l' : loc) : type := {|
    ty_own β' l := (⌜l `has_layout_loc` LPtr⌝ ∗ l ↦[β'] l' ∗ (l' ◁ₗ{own_state_min β' β} ty))%I;
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
      ty_layout := LPtr;
      ty_own_val v := (⌜v = val_of_loc l⌝ ∗ l ◁ₗ{β} ty)%I;
  |} |}.
  Next Obligation. iIntros (β ty l l'). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (β ty). by iDestruct 1 as (->) "_". Qed.
  Next Obligation. iIntros (β ty l l') "(%&Hl&Hl')". rewrite left_id. eauto with iFrame. Qed.
  Next Obligation. iIntros (β ty l l' v ?) "Hl [-> Hl']". iFrame. iSplit => //. by rewrite left_id. Qed.
  Next Obligation. done. Qed.

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
    typed_place (DerefPCtx Na1Ord LPtr :: K) l β1 (p @ (frac_ptr β ty1)) T.
  Proof.
    iIntros "HP" (Φ) "(%&Hm&Hl) HΦ" => /=.
    iApply @fupd_wp. iMod (heap_mapsto_own_state_to_mt with "Hm") as (q Hq) "Hm" => //.
    iApply (wp_deref with "Hm") => //; [naive_solver| by apply val_to_of_loc|].
    iIntros "!# !# Hm". iExists _. iSplit => //.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iFrame. iSplitR => //.
    by iApply heap_mapsto_own_state_from_mt.
  Qed.
  Global Instance type_place_frac_inst p β K β1 ty1 l :
    TypedPlace (DerefPCtx Na1Ord LPtr :: K) l β1 (p @ (frac_ptr β ty1)) :=
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

  Lemma simplify_frac_ptr_singleton_place_shr_to_own l p1 p2 β T:
    (⌜p1 = p2⌝ -∗ l ◁ₗ{β} p1 @ frac_ptr Own (singleton_place p2) -∗ T) -∗
    simplify_hyp (l ◁ₗ{β} p1 @ frac_ptr Shr (singleton_place p2)) T.
  Proof. iIntros "HT (%&Hl&%)". subst. iApply "HT" => //. by iFrame. Qed.
  Global Instance simplify_frac_ptr_singleton_place_inst l p1 p2 β:
    SimplifyHypPlace l β (p1 @ frac_ptr Shr (singleton_place p2)) (Some 50%N) :=
    λ T, i2p (simplify_frac_ptr_singleton_place_shr_to_own l p1 p2 β T).

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
    l ◁ᵥ l @ frac_ptr β (singleton_place l) ∗ T.
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

  Lemma type_cast_ptr_ptr p β ty T:
    (T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) -∗
    typed_un_op p (p ◁ₗ{β} ty)%I (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iApply wp_cast_loc. by apply val_to_of_loc.
    iApply ("HΦ" with "[Hp] HT") => //. by iFrame.
  Qed.
  Global Instance type_cast_ptr_ptr_inst (p : loc) β ty:
    TypedUnOp p (p ◁ₗ{β} ty)%I (CastOp PtrOp) PtrOp :=
    λ T, i2p (type_cast_ptr_ptr p β ty T).

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

  Lemma find_in_context_type_val_own l T:
    (∃ ty : type, l ◁ₗ ty ∗ T (t2mt (l @ frac_ptr Own ty))) -∗
    find_in_context (FindVal l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_type_val_own_inst (l : loc) :
    FindInContext (FindVal l) 1%nat :=
    λ T, i2p (find_in_context_type_val_own l T).

  Lemma find_in_context_type_val_own_singleton (l : loc) T:
    (True ∗ T (t2mt (l @ frac_ptr Own (singleton_place l)))) -∗
    find_in_context (FindVal l) T.
  Proof. iIntros "[_ HT]". iExists _ => /=. by iFrame. Qed.
  Global Instance find_in_context_type_val_own_singleton_inst (l : loc) :
    FindInContext (FindVal l) 2%nat :=
    λ T, i2p (find_in_context_type_val_own_singleton l T).

End own.

Notation "&frac{ β }" := (frac_ptr β) (format "&frac{ β }") : bi_scope.
Notation "&own" := (frac_ptr Own) (format "&own") : bi_scope.
Notation "&shr" := (frac_ptr Shr) (format "&shr") : bi_scope.

Section ptr.
  Context `{!typeG Σ}.

  Program Definition ptr : rtype := {|
    rty_type := loc;
    rty l' := {|
      ty_own β l := (⌜l `has_layout_loc` LPtr⌝ ∗ l ↦[β] l')%I;
  |} |}.
  Next Obligation. iIntros (????). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance rmovable_ptr : RMovable ptr := {|
    rmovable l := {|
      ty_layout := LPtr;
      ty_own_val v := (⌜v = val_of_loc l⌝)%I;
  |} |}.
  Next Obligation. iIntros (l l'). by iDestruct 1 as (?) "_". Qed.
  Next Obligation. iIntros (l v). by iDestruct 1 as %->. Qed.
  Next Obligation. iIntros (l v) "[_ Hl]". eauto with iFrame. Qed.
  Next Obligation. iIntros (l l' v ?) "Hl ->". by iFrame. Qed.
  Next Obligation. done. Qed.

  (* TODO: Think about this. This instance is probably not a good idea
  since it is not clear how the ownership is split. More specialized
  isntances like for uninit make more sense. *)
  (* Lemma type_add_frac_ptr v2 β ty T (p : loc) n: *)
  (*   (p ◁ₗ{β} ty -∗ v2 ◁ᵥ n @ int size_t -∗ T (val_of_loc (p +ₗ n)) (t2mt ((p +ₗ n) @ ptr))) -∗ *)
  (*     typed_bin_op v2 (v2 ◁ᵥ n @ int size_t) p (p ◁ₗ{β} ty) (PtrOffsetOp u8) (IntOp size_t) PtrOp T. *)
  (* Proof. *)
  (*   iIntros "HT" (Hint) "Hp". iIntros (Φ) "HΦ". *)
  (*   have ? := val_of_int_in_range _ _ _ Hint. *)
  (*   have ? := val_to_of_int _ _ _ Hint. *)
  (*   have ? := val_to_of_loc p. *)
  (*   iApply (wp_binop_det (p +ₗ n)). { *)
  (*     rewrite -(offset_loc_sz1 u8) //. *)
  (*     move => h v. split => Heq; subst. by inversion Heq; simplify_eq. econstructor => //. unfold it_in_range, it_min  in *. simpl in *. lia. *)
  (*   } *)
  (*   iApply ("HΦ" with "[]"). 2: by iApply ("HT" with "[$Hp//] []"). *)
  (*   done. *)
  (* Qed. *)
  (* Global Instance type_add_frac_ptr_inst v2 β ty T (p : loc) n: *)
  (*   TypedBinOp v2 (v2 ◁ᵥ n @ int size_t)%I p (p ◁ₗ{β} ty) (PtrOffsetOp u8) (IntOp size_t) PtrOp T := *)
  (*   i2p (type_add_frac_ptr v2 β ty T p n). *)

  (* Lemma type_rounddown_ptr v1 v2 P2 T p: *)
  (*   (⌜v1 = val_of_loc p⌝ -∗ P2 -∗ T (val_of_loc p) (t2mt (p @ ptr))) -∗ *)
  (*     typed_bin_op v1 (v1 ◁ᵥ p @ ptr) v2 P2 RoundDownOp T. *)
  (* Proof. *)
  (*   iIntros "HT -> Hv2". iIntros (Φ) "HΦ". *)
  (*   iApply wp_binop_det. by move => h /=; rewrite val_to_of_loc. *)
  (*   iApply ("HΦ" with "[]"); last by iApply "HT". *)
  (*   done. *)
  (* Qed. *)
  (* Global Instance type_rounddown_ptr_inst v1 v2 T p P2: *)
  (*   TypedBinOp v1 (v1 ◁ᵥ p @ ptr)%I v2 P2 RoundDownOp T := *)
  (*   i2p (type_rounddown_ptr v1 v2 P2 T p). *)

  Lemma simplify_ptr_hyp_place (p:loc) l T:
    (l ◁ₗ singleton_val LPtr (val_of_loc p) -∗ T) -∗
      simplify_hyp (l ◁ₗ p @ ptr) T.
  Proof.
    iIntros "HT [% Hl]". iApply "HT". by repeat iSplit.
  Qed.
  Global Instance simplify_ptr_hyp_place_inst p l:
    SimplifyHypPlace l Own (p @ ptr)%I (Some 50%N) :=
    λ T, i2p (simplify_ptr_hyp_place p l T).

  Lemma subsume_frac_ptr_learn_align l p β ty {HL: LearnAlignment β ty} T:
    ⌜l = p⌝ ∗ (l ◁ₗ{β} ty -∗ ⌜l `aligned_to` HL.(learnalign_align)⌝ -∗ T) -∗
    subsume (l ◁ₗ{β} ty) (l ◁ᵥ p @ ptr) T.
  Proof.
    iIntros "[-> HT] Hl". iSplitR => //.
    iDestruct ((learnalign_learn HL) with "Hl") as %?.
      by iApply ("HT" with "Hl").
  Qed.
  Global Instance subsume_frac_ptr_learn_align_inst l p β ty {HL: LearnAlignment β ty}:
    Subsume (l ◁ₗ{β} ty) (l ◁ᵥ p @ ptr)%I :=
    λ T, i2p (subsume_frac_ptr_learn_align l p β ty T).

  Lemma simplify_ptr_goal_val (p:loc) l T:
    T ⌜l = p⌝ -∗ simplify_goal (p ◁ᵥ l @ ptr) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros (->). Qed.
  Global Instance simplify_ptr_goal_val_inst (p : loc) l:
    SimplifyGoalVal p (l @ ptr)%I (Some 50%N) :=
    λ T, i2p (simplify_ptr_goal_val p l T).

End ptr.

Section null.
  Context `{!typeG Σ}.
  Program Definition null : type := {|
    ty_own β l := (⌜l `has_layout_loc` LPtr⌝ ∗ l ↦[β] NULL)%I;
  |}.
  Next Obligation. iIntros (???). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance movable_null : Movable null := {|
    ty_layout := LPtr;
    ty_own_val v := ⌜v = NULL⌝%I;
  |}.
  Next Obligation. by iIntros (?) "[% _]". Qed.
  Next Obligation. by iIntros (? ->). Qed.
  Next Obligation. iIntros (?) "[% ?]". iExists _. by iFrame. Qed.
  Next Obligation. iIntros (???) "? ->". by iFrame. Qed.

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
    (if b then op = NeOp else op = EqOp) →
    eval_bin_op op PtrOp PtrOp h p NULL v
     ↔ val_of_int (Z_of_bool b) i32 = Some v.
  Proof.
    move => ?.
    destruct b => //; split => Heq; subst; try by [inversion Heq; simplify_eq].
    all: econstructor; rewrite ?val_to_of_loc /val_of_bool/i2v ?Heq //.
  Qed.

  Lemma eval_bin_op_null_null (b : bool) op h v:
    (if b then op = EqOp else op = NeOp) →
    eval_bin_op op PtrOp PtrOp h NULL NULL v
     ↔ val_of_int (Z_of_bool b) i32 = Some v.
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
    iApply (wp_binop_det (i2v (Z_of_bool (if op is EqOp then true else false)) i32)).
    { move => ??. destruct op => //; split => Heq; subst; try by [inversion Heq]; by constructor. }
    iApply "HΦ" => //. by destruct op.
  Qed.
  Global Instance type_binop_null_null_inst v1 v2 op:
    TypedBinOp v1 (v1 ◁ᵥ null) v2 (v2 ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_null_null v1 v2 op T).

  Lemma type_binop_ptr_null v2 op T (l : loc) ty:
    (⌜match op with | EqOp | NeOp => True | _ => False end⌝ ∗ ∀ v, l ◁ₗ ty -∗
          T v (t2mt ((if op is EqOp then false else true) @ boolean i32))) -∗
    typed_bin_op l (l ◁ₗ ty) v2 (v2 ◁ᵥ null) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT] Hl" (-> Φ) "HΦ".
    iApply (wp_binop_det (i2v (Z_of_bool (if op is EqOp then false else true)) i32)).
    { move => ??. destruct op => //; split => Heq; subst; try by [inversion Heq].
      all: econstructor; rewrite ?val_to_of_loc /val_of_bool/i2v//. }
    iApply "HΦ". 2: by iApply "HT". by destruct op.
  Qed.
  Global Instance type_binop_ptr_null_inst v2 op (l : loc) ty:
    TypedBinOp l (l ◁ₗ ty) v2 (v2 ◁ᵥ null) op PtrOp PtrOp :=
    λ T, i2p (type_binop_ptr_null v2 op T l ty).

End null.

Section optionable.
  Context `{!typeG Σ}.

  Global Program Instance frac_ptr_optional ty β : ROptionable (frac_ptr β ty) null PtrOp PtrOp := {|
    ropt_opt x := {| opt_alt_sz := _ |}
  |}.
  Next Obligation. move => ty ??. done. Qed.
  Next Obligation.
    iIntros (ty β p bty beq v1 v2) "H1 ->".
    destruct bty. 1: iDestruct "H1" as (->) "_". 2: iDestruct "H1" as %->.
    all: iPureIntro => h v.
    1: by etrans; first apply (eval_bin_op_ptr_null (negb beq)); destruct beq => //.
    1: by etrans; first apply (eval_bin_op_null_null beq); destruct beq => //.
  Qed.
  Global Program Instance frac_ptr_optional_agree ty1 ty2 β : OptionableAgree (frac_ptr β ty1) (frac_ptr β ty2).
  Next Obligation. done. Qed.

  Global Program Instance ptr_optional : ROptionable ptr null PtrOp PtrOp := {|
    ropt_opt x := {| opt_alt_sz := _ |}
  |}.
  Next Obligation. move => ?. done. Qed.
  Next Obligation.
    iIntros (p bty beq v1 v2) "H1 ->".
    destruct bty. 1: iDestruct "H1" as %->. 2: iDestruct "H1" as %->.
    all: iPureIntro => h v.
    1: by etrans; first apply (eval_bin_op_ptr_null (negb beq)); destruct beq => //.
    1: by etrans; first apply (eval_bin_op_null_null beq); destruct beq => //.
  Qed.

  Lemma subsume_optional_place_val_null ty l β T b ty' `{!Movable ty} `{!Optionable ty null ot1 ot2}:
    (⌜b⌝ ∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null) T.
  Proof. iIntros "[% Hsub] Hl". iDestruct ("Hsub" with "Hl") as "[Hl $]". iLeft. by iFrame. Qed.
  Global Instance subsume_optional_place_val_null_inst ty l β b ty' `{!Movable ty} `{!Optionable ty null ot1 ot2}:
    Subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optional ty null)%I | 20 :=
    λ T, i2p (subsume_optional_place_val_null ty l β T b ty').

  Lemma subsume_optionalO_place_val_null A (ty : A → type) l β T b ty' `{!∀ x, Movable (ty x)} `{!∀ x, Optionable (ty x) null ot1 ot2}:
    (∃ x, ⌜b = Some x⌝ ∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ ty x) T) -∗ subsume (l ◁ₗ{β} ty') (l ◁ᵥ b @ optionalO ty null) T.
  Proof. iDestruct 1 as (x ->) "Hsub". iIntros "Hl". by iApply "Hsub". Qed.
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
