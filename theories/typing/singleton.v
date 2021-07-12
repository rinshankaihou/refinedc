From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section value.
  Context `{!typeG Σ}.

  Program Definition value (ly : layout) (v : val) : type := {|
    ty_own β l := (⌜l `has_layout_loc` ly⌝ ∗ ⌜v `has_layout_val` ly⌝ ∗ l ↦[β] v)%I;
  |}.
  Next Obligation. iIntros (?????) "[$ [$ ?]]". by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance movable_value ly v : Movable (value ly v) := {|
    ty_has_layout ly' := ly' = ly;
    ty_own_val v' := (⌜v `has_layout_val` ly⌝ ∗ ⌜v' = v⌝)%I;
  |}.
  Next Obligation. iIntros (ly v ly' l ->) "[%?]". done. Qed.
  Next Obligation. iIntros (ly v ly' v' ->) "[% ->]". done. Qed.
  Next Obligation. iIntros (ly v ly' l ->) "(%&%&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (ly v ly' l v' -> ?) "Hl [? ->]". by iFrame. Qed.

  Lemma value_simplify v T ly p:
    (⌜v = p⌝ -∗ ⌜v `has_layout_val` ly⌝ -∗ T) -∗
    simplify_hyp (v ◁ᵥ  value ly p) T.
  Proof. iIntros "HT [% ->]". by iApply "HT". Qed.
  Global Instance value_simplify_inst v ly p :
    SimplifyHypVal v (value ly p) (Some 0%N) :=
    λ T, i2p (value_simplify v T ly p).

  Lemma value_subsume_goal v v' ly ty `{!Movable ty} T:
    (⌜ty.(ty_has_layout) ly⌝ ∗ (v ◁ᵥ ty -∗ ⌜v = v'⌝ ∗ T)) -∗
    subsume (v ◁ᵥ ty) (v ◁ᵥ value ly v') T.
  Proof.
    iIntros "[% HT] Hty". iDestruct (ty_size_eq with "Hty") as %Hly; [done|].
    by iDestruct ("HT" with "Hty") as (->) "$".
  Qed.
  Global Instance value_subsume_goal_inst v v' ly ty `{!Movable ty}:
    SubsumeVal v ty (value ly v') :=
    λ T, i2p (value_subsume_goal v v' ly ty T).

  Lemma value_subsume_goal_loc l v' ly ty `{!Movable ty} T:
    (⌜ty.(ty_has_layout) ly⌝ ∗ ∀ v, v ◁ᵥ ty -∗ ⌜v = v'⌝ ∗ T) -∗
    subsume (l ◁ₗ ty) (l ◁ₗ value ly v') T.
  Proof.
    iIntros "[% HT] Hty".
    iDestruct (ty_aligned with "Hty") as %Hal; [done|].
    iDestruct (ty_deref with "Hty") as (v) "[Hmt Hty]"; [done|].
    iDestruct (ty_size_eq with "Hty") as %Hly; [done|].
    iDestruct ("HT" with "Hty") as (->) "$".
    by iFrame.
  Qed.
  Global Instance value_subsume_goal_loc_inst l v' ly ty `{!Movable ty}:
    SubsumePlace l Own ty (value ly v') :=
    λ T, i2p (value_subsume_goal_loc l v' ly ty T).

  Lemma value_merge v l ly T:
    (find_in_context (FindVal v) (λ ty:mtype, ⌜ty.(ty_has_layout) ly⌝ ∗ (l ◁ₗ ty -∗ T))) -∗
      simplify_hyp (l ◁ₗ value ly v) T.
  Proof.
    iDestruct 1 as (ty) "[Hv [% HT]]".
    iIntros "[% [% Hl]]". iApply "HT". by iApply (ty_ref with "[] Hl Hv").
  Qed.
  Global Instance value_merge_inst v l ly:
    SimplifyHypPlace l Own (value ly v)%I (Some 50%N) | 20 :=
    λ T, i2p (value_merge v l ly T).

  Lemma type_read_move T l ty ly a `{!Movable ty}:
    (⌜ty.(ty_has_layout) ly⌝ ∗ ∀ v, T v (value ly v) (t2mt ty)) -∗
      typed_read_end a l Own ty ly T.
  Proof.
    iIntros "[% HT] Hl".
    iApply fupd_mask_intro => //. iIntros "Hclose".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iExists _, _, _, (t2mt _). iFrame. do 2 iSplit => //=.
    iIntros "!# Hl". iMod "Hclose". iSplitR "HT" => //.
    by iFrame.
  Qed.
  Global Instance type_read_move_inst l ty ly a `{!Movable ty} :
    TypedReadEnd a l Own ty ly | 50 :=
    λ T, i2p (type_read_move T l ty ly a).

  (* TODO: this constraint on the layout is too strong, we only need
  that the length is the same and the alignment is lower. Adapt when necessary. *)
  Lemma type_write_own a ty `{!Movable ty} T l2 ty2 v `{!Movable ty2} ly:
    ⌜ty2.(ty_has_layout) ly⌝ ∗ (∀ v', v ◁ᵥ ty -∗ v' ◁ᵥ ty2 -∗ T (value ly v)) -∗
    typed_write_end a ly v ty l2 Own ty2 T.
  Proof.
    iDestruct 1 as (?) "HT". iIntros (?) "Hl Hv".
    iDestruct (ty_aligned with "Hl") as %?; [done|].
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']"; [done|].
    iDestruct (ty_size_eq with "Hv'") as %?; [done|].
    iApply fupd_mask_intro => //. iIntros "Hmask".
    iSplitL "Hl". { iExists _. by iFrame. }
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iDestruct (ty_size_eq with "Hv") as %?; [done|].
    iExists _. iDestruct ("HT" with "Hv Hv'") as "$". by iFrame.
  Qed.
  Global Instance type_write_own_inst a ty `{!Movable ty} l2 ty2 v `{!Movable ty2} ly:
    TypedWriteEnd a ly v ty l2 Own ty2 | 50 :=
    λ T, i2p (type_write_own a ty T l2 ty2 v ly).

End value.
Notation "value< ly , v >" := (value ly v) (only printing, format "'value<' ly ',' v '>'") : printing_sugar.


Section at_value.
  Context `{!typeG Σ}.

  (* TODO: At the moment this is hard-coded for void*. Generalize it to other layouts as well. *)
  Program Definition at_value (v : val) (ty : type) `{!Movable ty} : type := {|
    ty_own β l := (if β is Own then l ◁ₗ value void* v ∗ v ◁ᵥ ty else True )%I;
  |}.
  Next Obligation. by iIntros (??????) "?". Qed.

  Global Program Instance movable_at_value v ty `{!Movable ty} : Movable (at_value v ty) := {|
    ty_has_layout ly := ly = void*;
    ty_own_val v' := (v' ◁ᵥ value void* v ∗ v ◁ᵥ ty)%I;
  |}.
  Next Obligation. iIntros (v ty ? ly l ->) "[Hv ?]". by iApply (ty_aligned with "Hv"). Qed.
  Next Obligation. iIntros (v ty ? ? v' ->) "[Hv ?]". by iApply (ty_size_eq with "Hv"). Qed.
  Next Obligation.
    iIntros (v ty ? ly l ->) "[Hv ?]". iDestruct (ty_deref with "Hv") as (v') "[??]"; [done|]. iExists _. by iFrame.
  Qed.
  Next Obligation.
    iIntros (v ty ? l v' ? -> ?) "Hl [Hv ?]". iFrame. by iApply (ty_ref with "[] Hl Hv").
  Qed.

  Lemma at_value_simplify_hyp_val v v' ty `{!Movable ty} T:
    (v ◁ᵥ value void* v' -∗ v' ◁ᵥ ty -∗ T) -∗
    simplify_hyp (v ◁ᵥ at_value v' ty) T.
  Proof. iIntros "HT [??]". by iApply ("HT" with "[$] [$]"). Qed.
  Global Instance at_value_simplify_hyp_val_inst v v' ty `{!Movable ty} :
    SimplifyHypVal v (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_hyp_val v v' ty T).

  Lemma at_value_simplify_goal_val v v' ty `{!Movable ty} T:
    (T (v ◁ᵥ value void* v' ∗ v' ◁ᵥ ty)) -∗
    simplify_goal (v ◁ᵥ at_value v' ty) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "$". Qed.
  Global Instance at_value_simplify_goal_val_inst v v' ty `{!Movable ty} :
    SimplifyGoalVal v (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_goal_val v v' ty T).

  Lemma at_value_simplify_hyp_loc l v' ty `{!Movable ty} T:
    (l ◁ₗ value void* v' -∗ v' ◁ᵥ ty -∗ T) -∗
    simplify_hyp (l ◁ₗ at_value v' ty) T.
  Proof. iIntros "HT [??]". by iApply ("HT" with "[$] [$]"). Qed.
  Global Instance at_value_simplify_hyp_loc_inst l v' ty `{!Movable ty} :
    SimplifyHypPlace l Own (at_value v' ty) (Some 0%N) :=
    λ T, i2p (at_value_simplify_hyp_loc l v' ty T).

  Lemma at_value_simplify_goal_loc l v' ty `{!Movable ty} T:
    (T (l ◁ₗ value void* v' ∗ v' ◁ᵥ ty)) -∗
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

  Lemma typed_read_end_simpl l β ty ly n T {SH:SimplifyHyp (l ◁ₗ{β} ty) (Some n)} a:
    (SH (find_in_context (FindLoc l) (λ '(β2, ty2),
        typed_read_end a l β2 ty2 ly (λ v ty' ty3, l ◁ₗ{β2} ty' -∗ T v (place l) ty3)))).(i2p_P) -∗
    typed_read_end a l β ty ly T.
  Proof.
    iIntros "SH Hl". iDestruct (i2p_proof with "SH Hl") as ([β2 ty2]) "[Hl HP]".
    iMod ("HP" with "Hl") as (q v ty' ty3 ? ?) "(Hl & Hv & HP)". iIntros "!#".
    iExists _, _, _, _. iFrame. do 2 iSplit => //. iIntros "!# Hl".
    iMod ("HP" with "Hl") as "[Hl HT]". iModIntro. iSplitR; last by iApply "HT". done.
  Qed.
  Global Instance typed_read_end_simpl_inst l β ty ly n a `{!SimplifyHyp (l ◁ₗ{β} ty) (Some n)}:
    TypedReadEnd a l β ty ly | 1000 :=
    λ T, i2p (typed_read_end_simpl l β ty ly n T a).

  Lemma typed_write_end_simpl b ly v ty1 `{!Movable ty1} l β ty2 n T {SH:SimplifyHyp (l ◁ₗ{β} ty2) (Some n)}:
    (SH (find_in_context (FindLoc l) (λ '(β3, ty3),
        typed_write_end b ly v ty1 l β3 ty3 (λ ty', l ◁ₗ{β3} ty' -∗ T (place l))))).(i2p_P) -∗
    typed_write_end b ly v ty1 l β ty2 T.
  Proof.
    iIntros "SH % Hl Hv". iDestruct (i2p_proof with "SH Hl") as ([β3 ty3]) "[Hl HP]".
    iMod ("HP" with "[//] Hl Hv") as "[$ HP]". iIntros "!# !# Hl".
    iMod ("HP" with "Hl") as (ty') "[Hl HT]". iModIntro. iExists _. iSplitR; last by iApply "HT". done.
  Qed.
  Global Instance typed_write_end_simpl_inst b ly v ty1 `{!Movable ty1} l β ty2 n `{!SimplifyHyp (l ◁ₗ{β} ty2) (Some n)}:
    TypedWriteEnd b ly v ty1 l β ty2 | 1000 :=
    λ T, i2p (typed_write_end_simpl b ly v ty1 l β ty2 n T).

End place.
Notation "place< l >" := (place l) (only printing, format "'place<' l '>'") : printing_sugar.
