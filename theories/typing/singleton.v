From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section value.
  Context `{!typeG Σ}.

  Program Definition value (ot : op_type) (v : val) : type := {|
    ty_own β l := (⌜l `has_layout_loc` ot_layout ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ ⌜mem_cast_id v ot⌝ ∗ l ↦[β] v)%I;
  |}.
  Next Obligation. iIntros (?????) "[$ [$ [$ ?]]]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance movable_value ot v : Movable (value ot v) := {|
    ty_has_op_type ot' mt := is_value_ot ot ot';
    ty_own_val v' := (⌜mem_cast_id v ot⌝ ∗ ⌜v `has_layout_val` ot_layout ot⌝ ∗ ⌜v' = v⌝)%I;
  |}.
  Next Obligation. iIntros (ot v ot' mt l ->%is_value_ot_layout) "[%?]". done. Qed.
  Next Obligation. iIntros (ot v ot' mt v' ->%is_value_ot_layout) "[% [% ->]]". done. Qed.
  Next Obligation. iIntros (ot v ot' mt l _) "(%&%&%&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (ot v ot' mt l v' ->%is_value_ot_layout ?) "Hl [? [? ->]]". by iFrame. Qed.
  Next Obligation. iIntros (ot v v' ot' mt st ?). apply: mem_cast_compat_id. iPureIntro.
    move => [?[? ->]]. by destruct ot' => //; simplify_eq/=.
  Qed.

  Lemma value_simplify v T ot p:
    (⌜v = p⌝ -∗ ⌜v `has_layout_val` ot_layout ot⌝ -∗ ⌜mem_cast_id v ot⌝ -∗ T) -∗
    simplify_hyp (v ◁ᵥ  value ot p) T.
  Proof. iIntros "HT [% [% ->]]". by iApply "HT". Qed.
  Global Instance value_simplify_inst v ot p :
    SimplifyHypVal v (value ot p) (Some 0%N) :=
    λ T, i2p (value_simplify v T ot p).

  Lemma value_subsume_goal v v' ly ty `{!Movable ty} T:
    (⌜ty.(ty_has_op_type) ly MCId⌝ ∗ (v ◁ᵥ ty -∗ ⌜v = v'⌝ ∗ T)) -∗
    subsume (v ◁ᵥ ty) (v ◁ᵥ value ly v') T.
  Proof.
    iIntros "[% HT] Hty". iDestruct (ty_size_eq with "Hty") as %Hly; [done|].
    iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|].
    by iDestruct ("HT" with "Hty") as (->) "$".
  Qed.
  Global Instance value_subsume_goal_inst v v' ot ty `{!Movable ty}:
    SubsumeVal v ty (value ot v') :=
    λ T, i2p (value_subsume_goal v v' ot ty T).

  Lemma value_subsume_goal_loc l v' ot ty `{!Movable ty} T:
    (⌜ty.(ty_has_op_type) ot MCId⌝ ∗ ∀ v, v ◁ᵥ ty -∗ ⌜v = v'⌝ ∗ T) -∗
    subsume (l ◁ₗ ty) (l ◁ₗ value ot v') T.
  Proof.
    iIntros "[% HT] Hty".
    iDestruct (ty_aligned with "Hty") as %Hal; [done|].
    iDestruct (ty_deref with "Hty") as (v) "[Hmt Hty]"; [done|].
    iDestruct (ty_size_eq with "Hty") as %Hly; [done|].
    iDestruct (ty_memcast_compat_id with "Hty") as %?; [done|].
    iDestruct ("HT" with "Hty") as (->) "$".
    by iFrame.
  Qed.
  Global Instance value_subsume_goal_loc_inst l v' ot ty `{!Movable ty}:
    SubsumePlace l Own ty (value ot v') :=
    λ T, i2p (value_subsume_goal_loc l v' ot ty T).

  Lemma value_merge v l ot T:
    (find_in_context (FindVal v) (λ ty:mtype, ⌜ty.(ty_has_op_type) (UntypedOp (ot_layout ot)) MCNone⌝ ∗ (l ◁ₗ ty -∗ T))) -∗
      simplify_hyp (l ◁ₗ value ot v) T.
  Proof.
    iDestruct 1 as (ty) "[Hv [% HT]]".
    iIntros "[% [% [% Hl]]]". iApply "HT". by iApply (ty_ref with "[] Hl Hv").
  Qed.
  Global Instance value_merge_inst v l ot:
    SimplifyHypPlace l Own (value ot v)%I (Some 50%N) | 20 :=
    λ T, i2p (value_merge v l ot T).

  Lemma type_read_move T l ty ot a E `{!Movable ty} `{!CanSolve (ty.(ty_has_op_type) ot MCId)}:
    (∀ v, T v (value ot v) (t2mt ty)) -∗
      typed_read_end a E l Own ty ot T.
  Proof.
    unfold CanSolve, typed_read_end in *. iIntros "HT Hl".
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hclose".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iDestruct (ty_memcast_compat_id with "Hv") as %Hid; [done|].
    iExists _, _, (t2mt _). iFrame. do 2 iSplit => //=.
    iIntros "!# %st Hl Hv". iMod "Hclose".
    iExists _, (t2mt ty). rewrite Hid. iFrame "Hv". iSplitR "HT" => //.
    by iFrame.
  Qed.
  (* This needs to be a Hint Extern because the CanSolve depends on Movable *)
  Global Definition type_read_move_inst l ty ot a E `{!Movable ty} `{!CanSolve (ty.(ty_has_op_type) ot MCId)}:
    TypedReadEnd a E l Own ty ot :=
    λ T, i2p (type_read_move T l ty ot a E).

  (* TODO: this constraint on the layout is too strong, we only need
  that the length is the same and the alignment is lower. Adapt when necessary. *)
  Lemma type_write_own a ty `{!Movable ty} T E l2 ty2 v `{!Movable ty2} ot `{!CanSolve (ty.(ty_has_op_type) ot MCId)}:
    ⌜ty2.(ty_has_op_type) (UntypedOp (ot_layout ot)) MCNone⌝ ∗ (∀ v', v ◁ᵥ ty -∗ v' ◁ᵥ ty2 -∗ T (value ot v)) -∗
    typed_write_end a E ot v ty l2 Own ty2 T.
  Proof.
    unfold CanSolve, typed_write_end in *. iDestruct 1 as (?) "HT". iIntros "Hl Hv".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iDestruct (ty_size_eq with "Hv'") as %?; [done|].
    iDestruct (ty_memcast_compat_id with "Hv") as %Hid; [done|].
    iApply fupd_mask_intro; [destruct a; solve_ndisj|]. iIntros "Hmask".
    iSplit; [done|]. iSplitL "Hl". { iExists _. by iFrame. }
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iExists _. iDestruct ("HT" with "Hv Hv'") as "$". by iFrame.
  Qed.
  (* This needs to be a Hint Extern because the CanSolve depends on Movable *)
  Global Definition type_write_own_inst a ty `{!Movable ty} E l2 ty2 v `{!Movable ty2} ot `{!CanSolve (ty.(ty_has_op_type) ot MCId)}:
    TypedWriteEnd a E ot v ty l2 Own ty2 :=
    λ T, i2p (type_write_own a ty T E l2 ty2 v ot).
End value.
Notation "value< ot , v >" := (value ot v) (only printing, format "'value<' ot ',' v '>'") : printing_sugar.

Global Hint Extern 50 (TypedReadEnd _ _ _ Own _ _) =>
  unshelve notypeclasses refine (type_read_move_inst _ _ _ _ _ ) : typeclass_instances.
Global Hint Extern 50 (TypedWriteEnd _ _ _ _ _ _ Own _) =>
  unshelve notypeclasses refine (type_write_own_inst _ _ _ _ _ _ _) : typeclass_instances.


Section at_value.
  Context `{!typeG Σ}.

  (* TODO: At the moment this is hard-coded for PtrOp. Generalize it to other layouts as well. *)
  Program Definition at_value (v : val) (ty : type) `{!Movable ty} : type := {|
    ty_own β l := (if β is Own then l ◁ₗ value PtrOp v ∗ v ◁ᵥ ty else True )%I;
  |}.
  Next Obligation. by iIntros (??????) "?". Qed.

  Global Program Instance movable_at_value v ty `{!Movable ty} : Movable (at_value v ty) := {|
    ty_has_op_type ot mt := is_value_ot PtrOp ot;
    ty_own_val v' := (v' ◁ᵥ value PtrOp v ∗ v ◁ᵥ ty)%I;
  |}.
  Next Obligation. iIntros (v ty ? ot mt l ?) "[Hv ?]". by iApply (ty_aligned with "Hv"). Qed.
  Next Obligation. iIntros (v ty ? ot mt v' ?) "[Hv ?]". by iApply (ty_size_eq with "Hv"). Qed.
  Next Obligation. iIntros (v ty ? ot mt l ?) "[Hv $]". by iApply (ty_deref with "Hv"). Qed.
  Next Obligation. iIntros (v ty ? ot mt l v' ? ?) "Hl [Hv $]". by iApply (ty_ref with "[] Hl Hv"). Qed.
  Next Obligation.
    iIntros (v ty ? v' ot mt st ?) "[Hv ?]".
    iDestruct (ty_memcast_compat with "Hv") as "?"; [done|]. destruct mt => //. iFrame.
  Qed.


  Lemma at_value_simplify_hyp_val v v' ty `{!Movable ty} T:
    (v ◁ᵥ value PtrOp v' -∗ v' ◁ᵥ ty -∗ T) -∗
    simplify_hyp (v ◁ᵥ at_value v' ty) T.
  Proof. iIntros "HT [??]". by iApply ("HT" with "[$] [$]"). Qed.
  Global Instance at_value_simplify_hyp_val_inst v v' ty `{!Movable ty} :
    SimplifyHypVal v (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_hyp_val v v' ty T).

  Lemma at_value_simplify_goal_val v v' ty `{!Movable ty} T:
    (T (v ◁ᵥ value PtrOp v' ∗ v' ◁ᵥ ty)) -∗
    simplify_goal (v ◁ᵥ at_value v' ty) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "$". Qed.
  Global Instance at_value_simplify_goal_val_inst v v' ty `{!Movable ty} :
    SimplifyGoalVal v (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_goal_val v v' ty T).

  Lemma at_value_simplify_hyp_loc l v' ty `{!Movable ty} T:
    (l ◁ₗ value PtrOp v' -∗ v' ◁ᵥ ty -∗ T) -∗
    simplify_hyp (l ◁ₗ at_value v' ty) T.
  Proof. iIntros "HT [??]". by iApply ("HT" with "[$] [$]"). Qed.
  Global Instance at_value_simplify_hyp_loc_inst l v' ty `{!Movable ty} :
    SimplifyHypPlace l Own (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_hyp_loc l v' ty T).

  Lemma at_value_simplify_goal_loc l v' ty `{!Movable ty} T:
    (T (l ◁ₗ value PtrOp v' ∗ v' ◁ᵥ ty)) -∗
    simplify_goal (l ◁ₗ at_value v' ty) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "$". Qed.
  Global Instance at_value_simplify_goal_loc_inst l v' ty `{!Movable ty} :
    SimplifyGoalPlace l Own (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_goal_loc l v' ty T).

End at_value.
Notation "at_value< v , ty >" := (at_value v ty) (only printing, format "'at_value<' v ',' ty '>'") : printing_sugar.
Typeclasses Opaque at_value.

Section place.
  Context `{!typeG Σ}.

  Program Definition place (l : loc) : type := {|
    ty_own β l' := (⌜l = l'⌝)%I;
  |}.
  Next Obligation. by iIntros (????) "$". Qed.

  Lemma place_simplify l β T p:
    (⌜l = p⌝ -∗ T) -∗
    simplify_hyp (l◁ₗ{β} place p) T.
  Proof. iIntros "HT ->". by iApply "HT". Qed.
  Global Instance place_simplify_inst l β p :
    SimplifyHypPlace l β (place p)%I (Some 0%N) :=
    λ T, i2p (place_simplify l β T p).

  Lemma place_simplify_goal l β T p:
    (T ⌜l = p⌝) -∗
    simplify_goal (l◁ₗ{β} place p) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "->". Qed.
  Global Instance place_simplify_goal_inst l β p :
    SimplifyGoalPlace l β (place p)%I (Some 0%N) :=
    λ T, i2p (place_simplify_goal l β T p).


  Lemma type_addr_of_singleton l β ty T:
    T β ty (place l) -∗
    typed_addr_of_end l β ty T.
  Proof. iIntros "HT Hl !#". iExists _, _, _. iFrame "HT". by iFrame. Qed.
  Global Instance type_addr_of_singleton_inst l β ty:
    TypedAddrOfEnd l β ty :=
    λ T, i2p (type_addr_of_singleton l β ty T).

  Lemma typed_place_simpl P l ty1 β1 T n {SH:SimplifyHyp (l ◁ₗ{β1} ty1) (Some n)}:
    (SH (find_in_context (FindLoc l) (λ '(β2, ty2),
        typed_place P l β2 ty2 (λ l3 β3 ty3 typ R,
           T l3 β3 ty3 (λ _, place l) (λ ty', l ◁ₗ{β2} typ ty' ∗ R ty' ))))).(i2p_P) -∗
    typed_place P l β1 ty1 T.
  Proof.
    iIntros "SH" (Φ) "Hl HΦ".
    iDestruct (i2p_proof with "SH Hl") as ([β2 ty2]) "[Hl HP]".
    iApply ("HP" with "Hl").
    iIntros (l3 β3 ty3 typ R) "Hl Hc HT".
    iApply ("HΦ" with "Hl [Hc] HT").
    iIntros (ty') "Hl3". by iMod ("Hc" with "Hl3") as "[$ $]".
  Qed.
  Global Instance typed_place_simpl_inst P l ty1 β1 n `{!SimplifyHyp (l ◁ₗ{β1} ty1) (Some n)}:
    TypedPlace P l β1 ty1 | 1000 :=
    λ T, i2p (typed_place_simpl P l ty1 β1 T n).

  Lemma typed_read_end_simpl E l β ty ly n T {SH:SimplifyHyp (l ◁ₗ{β} ty) (Some n)} a:
    (SH (find_in_context (FindLoc l) (λ '(β2, ty2),
        typed_read_end a E l β2 ty2 ly (λ v ty' ty3, l ◁ₗ{β2} ty' -∗ T v (place l) ty3)))).(i2p_P) -∗
    typed_read_end a E l β ty ly T.
  Proof.
    iIntros "SH". iApply typed_read_end_mono_strong; [done|]. iIntros "Hl !>".
    iDestruct (i2p_proof with "SH Hl") as ([β2 ty2]) "[Hl HP]" => /=.
    iExists _, _, True%I. iFrame. iSplit; [done|].
    iApply (typed_read_end_wand with "HP"). iIntros (v ty1 ty2') "HT _ Hl Hv !>".
    iExists (place l), _. iFrame. iSplit; [done|]. by iApply "HT".
  Qed.
  Global Instance typed_read_end_simpl_inst E l β ty ly n a `{!SimplifyHyp (l ◁ₗ{β} ty) (Some n)}:
    TypedReadEnd a E l β ty ly | 1000 :=
    λ T, i2p (typed_read_end_simpl E l β ty ly n T a).

  Lemma typed_write_end_simpl b E ot v ty1 `{!Movable ty1} l β ty2 n T {SH:SimplifyHyp (l ◁ₗ{β} ty2) (Some n)}:
    (SH (find_in_context (FindLoc l) (λ '(β3, ty3),
        typed_write_end b E ot v ty1 l β3 ty3 (λ ty', l ◁ₗ{β3} ty' -∗ T (place l))))).(i2p_P) -∗
    typed_write_end b E ot v ty1 l β ty2 T.
  Proof.
    iIntros "SH". iApply typed_write_end_mono_strong; [done|]. iIntros "Hv Hl !>".
    iDestruct (i2p_proof with "SH Hl") as ([β2' ty2']) "[Hl HP]" => /=.
    iExists (t2mt _), _, _, True%I. iFrame. iSplit; [done|].
    iApply (typed_write_end_wand with "HP"). iIntros (ty3) "HT _ Hl !>".
    iExists (place l). iSplit; [done|]. by iApply "HT".
  Qed.
  Global Instance typed_write_end_simpl_inst b E ot v ty1 `{!Movable ty1} l β ty2 n `{!SimplifyHyp (l ◁ₗ{β} ty2) (Some n)}:
    TypedWriteEnd b E ot v ty1 l β ty2 | 1000 :=
    λ T, i2p (typed_write_end_simpl b E ot v ty1 l β ty2 n T).

End place.
Notation "place< l >" := (place l) (only printing, format "'place<' l '>'") : printing_sugar.
