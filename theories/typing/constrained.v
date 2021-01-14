From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional.
Set Default Proof Using "Type".

Class OwnConstraint `{!typeG Σ} (P : own_state → iProp Σ) : Prop := {
  own_constraint_persistent : Persistent (P Shr);
  own_constraint_share E : ↑shrN ⊆ E → P Own ={E}=∗ P Shr;
}.
Global Existing Instance own_constraint_persistent.

Section own_constrained.
  Context `{!typeG Σ}.

  Program Definition own_constrained (P : own_state → iProp Σ) `{!OwnConstraint P} (ty : type) : type := {|
    ty_own β l := (l ◁ₗ{β} ty ∗ P β)%I
  |}.
  Next Obligation.
    move => ty P ? l E ?. iIntros "[Hl HP]".
    iMod (ty_share with "Hl") as "$" => //.
    by iApply own_constraint_share.
  Qed.

  Global Instance own_constrained_rty_ne n P `{!OwnConstraint P} : Proper ((dist n) ==> (dist n)) (own_constrained P).
  Proof. solve_type_proper. Qed.
  Global Instance own_constrained_rty_proper P `{!OwnConstraint P} : Proper ((≡) ==> (≡)) (own_constrained P).
  Proof. solve_type_proper. Qed.

  Global Program Instance own_constrained_movable ty P `{!Movable ty} `{!OwnConstraint P} : Movable (own_constrained P ty) := {|
     ty_layout := ty.(ty_layout);
     ty_own_val v := (v ◁ᵥ ty ∗ P Own)%I;
  |}.
  Next Obligation. iIntros (?????) "[? _]". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (?????) "[? _]". by iApply ty_size_eq. Qed.
  Next Obligation. iIntros (?????) "[? $]". by iApply ty_deref. Qed.
  Next Obligation. iIntros (???????) "Hl [? $]". by iApply (ty_ref with "[//] [Hl]"). Qed.

  Global Instance own_constrained_loc_in_bounds ty β P `{!OwnConstraint P} `{!LocInBounds ty β} :
    LocInBounds (own_constrained P ty) β.
  Proof.
    constructor. iIntros (l) "[Hl _]". by iApply loc_in_bounds_in_bounds.
  Qed.

  Lemma simplify_hyp_place_own_constrained P l β ty T `{!OwnConstraint P}:
    (P β -∗ l ◁ₗ{β} ty -∗ T) -∗ simplify_hyp (l◁ₗ{β} own_constrained P ty) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Global Instance simplify_hyp_place_own_constrained_inst P l β ty `{!OwnConstraint P}:
    SimplifyHypPlace l β (own_constrained P ty)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_own_constrained P l β ty T).

  Lemma simplify_goal_place_own_constrained P l β ty T `{!OwnConstraint P}:
    T (l ◁ₗ{β} ty ∗ P β) -∗ simplify_goal (l◁ₗ{β} own_constrained P ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ $]". Qed.
  Global Instance simplify_goal_place_own_constrained_inst P l β ty `{!OwnConstraint P}:
    SimplifyGoalPlace l β (own_constrained P ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_place_own_constrained P l β ty T).

  Lemma simplify_hyp_val_own_constrained P v ty T `{!Movable ty} `{!OwnConstraint P}:
    (P Own -∗ v ◁ᵥ ty -∗ T) -∗ simplify_hyp (v ◁ᵥ own_constrained P ty) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Global Instance simplify_hyp_val_own_constrained_inst P v ty `{!Movable ty} `{!OwnConstraint P}:
    SimplifyHypVal v (own_constrained P ty)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_val_own_constrained P v ty T).

  Lemma simplify_goal_val_own_constrained P v ty T `{!Movable ty} `{!OwnConstraint P}:
    T (v ◁ᵥ ty ∗ P Own) -∗ simplify_goal (v ◁ᵥ own_constrained P ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ $]". Qed.
  Global Instance simplify_goal_val_own_constrained_inst P v ty `{!Movable ty} `{!OwnConstraint P}:
    SimplifyGoalVal v (own_constrained P ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_val_own_constrained P v ty T).

  Global Program Instance own_constrained_optional ty P optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!OwnConstraint P} `{!Optionable ty optty ot1 ot2} : Optionable (own_constrained P ty) optty ot1 ot2 := {|
    opt_pre v1 v2 := opt_pre ty v1 v2
  |}.
  Next Obligation. move => ????????? /=. apply opt_alt_sz. Qed.
  Next Obligation.
    iIntros (?????????[]?????) "Hpre H1 H2". 1: iDestruct "H1" as "[H1 _]".
    by iApply (opt_bin_op true with "Hpre H1 H2").
    by iApply (opt_bin_op false with "Hpre H1 H2").
  Qed.

  Global Instance optionable_agree_own_constrained P (ty2 : type) `{!OwnConstraint P} `{!OptionableAgree ty1 ty2} : OptionableAgree (own_constrained P ty1) ty2.
  Proof. done. Qed.


  Definition tyown_constraint (l : loc) (ty : type) (β : own_state) : iProp Σ := l ◁ₗ{β} ty.

  Global Program Instance tyown_constraint_own_constraint l ty: OwnConstraint (tyown_constraint l ty).
  Next Obligation. move => ???. apply: ty_share. Qed.

  Lemma simplify_hyp_place_tyown_constrained l β ty T:
    (l ◁ₗ{β} ty -∗ T) -∗ simplify_hyp (tyown_constraint l ty β) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_place_tyown_constrained_inst l β ty:
    SimplifyHyp (tyown_constraint l ty β) (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_tyown_constrained l β ty T).

  Lemma simplify_goal_place_tyown_constrained l β ty T:
    T (l ◁ₗ{β} ty) -∗ simplify_goal (tyown_constraint l ty β) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "$". Qed.
  Global Instance simplify_goal_place_tyown_constrained_inst l β ty:
    SimplifyGoal (tyown_constraint l ty β) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_tyown_constrained l β ty T).
End own_constrained.

Typeclasses Opaque own_constrained tyown_constraint.
Arguments tyown_constraint : simpl never.

Section constrained.
  Context `{!typeG Σ}.

  Definition persistent_own_constraint (P : iProp Σ) (β : own_state) : iProp Σ := □ P.

  Global Instance persistent_own_constraint_inst P: OwnConstraint (persistent_own_constraint P).
  Proof. constructor; [by apply _ | by iIntros (??) "H !>"]. Qed.

  Lemma simplify_hyp_place_persistent_constrained P β T:
    (P -∗ T) -∗ simplify_hyp (persistent_own_constraint P β) T.
  Proof. iIntros "HT #Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_place_persistent_constrained_inst P β:
    SimplifyHyp (persistent_own_constraint P β) (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_persistent_constrained P β T).

  Lemma simplify_goal_place_persistent_constrained P `{!Persistent P} β T:
    T P -∗ simplify_goal (persistent_own_constraint P β) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "#$". Qed.
  Global Instance simplify_goal_place_persistent_constrained_inst P `{!Persistent P} β:
    SimplifyGoal (persistent_own_constraint P β) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_persistent_constrained P β T).
End constrained.

Typeclasses Opaque persistent_own_constraint.
Arguments persistent_own_constraint : simpl never.

Notation constrained ty P := (own_constrained (persistent_own_constraint P) ty).

Section nonshr_constrained.
  Context `{!typeG Σ}.

  Definition nonshr_constraint (P : iProp Σ) (β : own_state) : iProp Σ :=
    match β with | Own => P | Shr => True end.

  Global Program Instance nonshr_constraint_own_constraint P: OwnConstraint (nonshr_constraint P).
  Next Obligation. iIntros (???) "?". done. Qed.

  Lemma simplify_hyp_place_nonshr_constrained P T:
    (P -∗ T) -∗ simplify_hyp (nonshr_constraint P Own) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_place_nonshr_constrained_inst P:
    SimplifyHyp (nonshr_constraint P Own) (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_nonshr_constrained P T).

  Lemma simplify_goal_place_nonshr_constrained P T:
    T P -∗ simplify_goal (nonshr_constraint P Own) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "$". Qed.
  Global Instance simplify_goal_place_nonshr_constrained_inst P:
    SimplifyGoal (nonshr_constraint P Own) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_nonshr_constrained P T).

End nonshr_constrained.

Typeclasses Opaque nonshr_constraint.
Arguments nonshr_constraint : simpl never.
