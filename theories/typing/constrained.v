From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional.
Set Default Proof Using "Type".

Section constrained.
  Context `{!typeG Σ}.

  Program Definition constrained (ty : type) (P : iProp Σ) : type := {|
    ty_own β l := (l ◁ₗ{β} ty ∗ □ P)%I
  |}.
  Next Obligation. move => ty P ? l ?. iIntros "[H $]". by iApply ty_share. Qed.

  Global Instance constrained_rty_ne n : Proper ((dist n) ==> (dist n) ==> (dist n)) constrained.
  Proof. solve_type_proper. Qed.
  Global Instance constrained_rty_proper : Proper ((≡) ==> (≡) ==> (≡)) constrained.
  Proof. solve_type_proper. Qed.

  Global Program Instance constrained_movable ty P `{!Movable ty} : Movable (constrained ty P) := {|
     ty_layout := ty.(ty_layout);
     ty_own_val v := (v ◁ᵥ ty ∗ □ P)%I;
  |}.
  Next Obligation. iIntros (????) "[? _]". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (????) "[? _]". by iApply ty_size_eq. Qed.
  Next Obligation. iIntros (????) "[? $]". by iApply ty_deref. Qed.
  Next Obligation. iIntros (??????) "Hl [? $]". by iApply (ty_ref with "[//] [Hl]"). Qed.

  Global Instance constrained_loc_in_bounds ty β P `{!LocInBounds ty β} :
    LocInBounds (constrained ty P) β.
  Proof.
    constructor. iIntros (l) "[Hl _]". by iApply loc_in_bounds_in_bounds.
  Qed.

  Lemma simplify_hyp_place_constrained P l β ty T `{!Persistent P}:
    (P -∗ l ◁ₗ{β} ty -∗ T) -∗ simplify_hyp (l◁ₗ{β} constrained ty P) T.
  Proof. iIntros "HT [Hl #?]". by iApply "HT". Qed.
  Global Instance simplify_hyp_place_constrained_inst P l β ty `{!Persistent P}:
    SimplifyHypPlace l β (constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_constrained P l β ty T).

  Lemma simplify_goal_place_constrained P l β ty T `{!Persistent P}:
    T (l ◁ₗ{β} ty ∗ P) -∗ simplify_goal (l◁ₗ{β} constrained ty P) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ #?]". by iModIntro. Qed.
  Global Instance simplify_goal_place_constrained_inst P l β ty `{!Persistent P}:
    SimplifyGoalPlace l β (constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_place_constrained P l β ty T).

  Lemma simplify_hyp_val_constrained P v ty T `{!Movable ty}:
    (P -∗ v ◁ᵥ ty -∗ T) -∗ simplify_hyp (v◁ᵥ constrained ty P) T.
  Proof. iIntros "HT [Hl #?]". by iApply "HT". Qed.
  Global Instance simplify_hyp_val_constrained_inst P v ty `{!Movable ty}:
    SimplifyHypVal v (constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_val_constrained P v ty T).

  Lemma simplify_goal_val_constrained P v ty T `{!Movable ty} `{!Persistent P}:
    T (v ◁ᵥ ty ∗ P) -∗ simplify_goal (v◁ᵥ constrained ty P) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ #?]". by iModIntro. Qed.
  Global Instance simplify_goal_val_constrained_inst P v ty `{!Movable ty} `{!Persistent P}:
    SimplifyGoalVal v (constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_val_constrained P v ty T).

  Global Program Instance constrained_optional ty P optty ot1 ot2 `{!Movable ty} `{!Movable optty} `{!Optionable ty optty ot1 ot2} : Optionable (constrained ty P) optty ot1 ot2 := {|
    opt_pre v1 v2 := opt_pre ty v1 v2
  |}.
  Next Obligation. move => ???????? /=. apply opt_alt_sz. Qed.
  Next Obligation.
    iIntros (????????[]?????) "Hpre H1 H2". 1: iDestruct "H1" as "[H1 _]".
    by iApply (opt_bin_op true with "Hpre H1 H2").
    by iApply (opt_bin_op false with "Hpre H1 H2").
  Qed.

  Global Instance optionable_agree_constrained P (ty2 : type) `{!OptionableAgree ty1 ty2} : OptionableAgree (constrained ty1 P) ty2.
  Proof. done. Qed.
End constrained.
Typeclasses Opaque constrained.


Class OwnConstraint `{!typeG Σ} (P : own_state → iProp Σ) : Prop := {
  own_constraint_persistent : Persistent (P Shr);
  own_constraint_share E : ↑shrN ⊆ E → P Own ={E}=∗ P Shr;
}.
Global Existing Instance own_constraint_persistent.

Section own_constrained.
  Context `{!typeG Σ}.

  Program Definition own_constrained (ty : type) (P : own_state → iProp Σ) `{!OwnConstraint P} : type := {|
    ty_own β l := (l ◁ₗ{β} ty ∗ P β)%I
  |}.
  Next Obligation.
    move => ty P ? l E ?. iIntros "[Hl HP]".
    iMod (ty_share with "Hl") as "$" => //.
    by iApply own_constraint_share.
  Qed.

  Global Program Instance own_constrained_movable ty P `{!Movable ty}  `{!OwnConstraint P} : Movable (own_constrained ty P) := {|
     ty_layout := ty.(ty_layout);
     ty_own_val v := (v ◁ᵥ ty ∗ P Own)%I;
  |}.
  Next Obligation. iIntros (?????) "[? _]". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (?????) "[? _]". by iApply ty_size_eq. Qed.
  Next Obligation. iIntros (?????) "[? $]". by iApply ty_deref. Qed.
  Next Obligation. iIntros (???????) "Hl [? $]". by iApply (ty_ref with "[//] [Hl]"). Qed.

  Lemma simplify_hyp_place_own_constrained P l β ty T `{!OwnConstraint P}:
    (P β -∗ l ◁ₗ{β} ty -∗ T) -∗ simplify_hyp (l◁ₗ{β} own_constrained ty P) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Global Instance simplify_hyp_place_own_constrained_inst P l β ty `{!OwnConstraint P}:
    SimplifyHypPlace l β (own_constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_own_constrained P l β ty T).

  Lemma simplify_goal_place_own_constrained P l β ty T `{!OwnConstraint P}:
    T (l ◁ₗ{β} ty ∗ P β) -∗ simplify_goal (l◁ₗ{β} own_constrained ty P) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ $]". Qed.
  Global Instance simplify_goal_place_own_constrained_inst P l β ty `{!OwnConstraint P}:
    SimplifyGoalPlace l β (own_constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_place_own_constrained P l β ty T).

  Lemma simplify_hyp_val_own_constrained P v ty T `{!Movable ty} `{!OwnConstraint P}:
    (P Own -∗ v ◁ᵥ ty -∗ T) -∗ simplify_hyp (v ◁ᵥ own_constrained ty P) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Global Instance simplify_hyp_val_own_constrained_inst P v ty `{!Movable ty} `{!OwnConstraint P}:
    SimplifyHypVal v (own_constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_val_own_constrained P v ty T).

  Lemma simplify_goal_val_own_constrained P v ty T `{!Movable ty} `{!OwnConstraint P}:
    T (v ◁ᵥ ty ∗ P Own) -∗ simplify_goal (v ◁ᵥ own_constrained ty P) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[$ $]". Qed.
  Global Instance simplify_goal_val_own_constrained_inst P v ty `{!Movable ty} `{!OwnConstraint P}:
    SimplifyGoalVal v (own_constrained ty P)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_val_own_constrained P v ty T).


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
