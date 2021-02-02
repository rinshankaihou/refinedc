From refinedc.typing Require Export type.
From refinedc.typing Require Import programs optional.
Set Default Proof Using "Type".

Definition ty_exists_rty_def `{!typeG Σ} {A} (ty : A → type) (a : A) : type := ty a.
Definition ty_exists_rty_aux : seal (@ty_exists_rty_def). by eexists. Qed.
Definition ty_exists_rty := (ty_exists_rty_aux).(unseal).
Definition ty_exists_rty_eq : ty_exists_rty = @ty_exists_rty_def := (ty_exists_rty_aux).(seal_eq).
Arguments ty_exists_rty {_ _ _} _ _.

Section tyexist.
  Context `{!typeG Σ} {A : Type}.

  (* rty has to be sealed as unification goes crazy otherwise (it will
  unify everything with tyexists). However rty_type must not use
  opaque as it cannot be unified with A otherwise by typeclass
  search. *)
  Program Definition tyexists (ty : A → type) : rtype := {|
     rty_type := A;
     rty x := ty_exists_rty ty x
  |}.

  Lemma tyexists_eq ty (x : A) :
    (x @ tyexists ty = ty x)%I.
  Proof. by rewrite /with_refinement/= ty_exists_rty_eq. Qed.

  Global Instance ty_exists_rty_ne n : Proper (pointwise_relation A (dist n) ==> (=) ==> (dist n)) ty_exists_rty.
  Proof. rewrite ty_exists_rty_eq. solve_type_proper. Qed.
  Global Instance ty_exists_rty_proper : Proper (pointwise_relation A (≡) ==> (=) ==> (≡)) ty_exists_rty.
  Proof. rewrite ty_exists_rty_eq. solve_type_proper. Qed.

  (* This has to be a definition with Hint Extern for goal to get solved in the right order *)
  (* TODO: should this use TCEq or LayoutEq? LayoutEq seems to break randomly for unknown reasons. *)
  Global Program Definition tyexists_movable ty `{!∀ x, Movable (ty x)} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)} : RMovable (tyexists ty) := {|
    rmovable x := {|
      ty_layout := (ty x).(ty_layout);
      ty_own_val := (ty x).(ty_own_val);
  |} |}.
  Next Obligation. iIntros (ty ? ? x l). rewrite tyexists_eq. by apply ty_aligned. Qed.
  Next Obligation. iIntros (ty ? ? x v). by apply ty_size_eq. Qed.
  Next Obligation. iIntros (ty ? ? x l). rewrite tyexists_eq. by apply ty_deref. Qed.
  Next Obligation. iIntros (ty ? ? x l v). rewrite tyexists_eq. by apply ty_ref. Qed.
  Next Obligation. move => ?? H x1 x2 /=. move: (H x1 x2). by inversion 1. Qed.

  Global Instance tyexists_loc_in_bounds ty β n `{!∀ x, LocInBounds (ty x) β n} :
    LocInBounds (tyexists ty) β n.
  Proof.
    constructor. iIntros (l) "Hl". iDestruct "Hl" as (x) "Hl".
    rewrite tyexists_eq. by iApply loc_in_bounds_in_bounds.
  Qed.
End tyexist.

Hint Extern 1 (RMovable (tyexists _)) => simple notypeclasses refine (@tyexists_movable _ _ _ _ _ _) => /= : typeclass_instances.

Section tyexist.
  Context `{!typeG Σ} {A : Type}.

  Lemma simplify_hyp_place_tyexists x l β (ty : A → _) T:
    (l ◁ₗ{β} ty x -∗ T) -∗ simplify_hyp (l◁ₗ{β} x @ tyexists ty) T.
  Proof. iIntros "HT Hl". rewrite tyexists_eq. by iApply "HT". Qed.
  Global Instance simplify_hyp_place_tyexists_inst x l β ty :
    SimplifyHypPlace l β (x @ tyexists ty)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_tyexists x l β ty T).

  Lemma simplify_goal_place_tyexists x l β (ty : A → _) T:
    T (l ◁ₗ{β} ty x) -∗ simplify_goal (l◁ₗ{β} x @ tyexists ty) T.
  Proof. iIntros "HT". rewrite tyexists_eq. iExists _. iFrame. by iIntros "?". Qed.
  Global Instance simplify_goal_place_tyexists_inst x l β ty :
    SimplifyGoalPlace l β (x @ tyexists ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_place_tyexists x l β ty T).

  Lemma simplify_hyp_val_tyexists x v ty T `{!∀ x, Movable (ty x)} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)}:
    (v ◁ᵥ ty x -∗ T) -∗ simplify_hyp (v◁ᵥ x @ tyexists (A:=A) ty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_val_tyexists_inst x v ty `{!∀ x, Movable (ty x)} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)}:
    SimplifyHypVal v (x @ tyexists ty)%I (Some 0%N) :=
    λ T, i2p (simplify_hyp_val_tyexists x v ty T).

  Lemma simplify_goal_val_tyexists x v ty T `{!∀ x, Movable (ty x)} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)}:
    T (v ◁ᵥ ty x) -∗ simplify_goal (v◁ᵥ x @ tyexists (A:=A) ty) T.
  Proof. iIntros "HT". iExists _. iFrame. by iIntros "?". Qed.
  Global Instance simplify_goal_val_tyexists_inst x v ty `{!∀ x, Movable (ty x)} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)}:
    SimplifyGoalVal v (x @ tyexists ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_val_tyexists x v ty T).

  Global Instance simple_subsume_place_tyexists_l (ty1 : A → _) x ty2 `{!SimpleSubsumePlace (ty1 x) ty2 P}:
    SimpleSubsumePlace (x @ tyexists ty1) ty2 P.
  Proof. iIntros (l β) "HP Hl". rewrite ! tyexists_eq. iApply (@simple_subsume_place with "HP Hl"). Qed.

  Global Instance simple_subsume_place_tyexists_r (ty2 : A → _) x ty1 `{!SimpleSubsumePlace ty1 (ty2 x) P}:
    SimpleSubsumePlace ty1 (x @ tyexists ty2) P.
  Proof. iIntros (l β) "HP Hl". rewrite ! tyexists_eq. iApply (@simple_subsume_place with "HP Hl"). Qed.

  Global Program Instance tyexist_optional (ty : A → _) optty ot1 ot2 `{!∀ x, Movable (ty x)} `{!Movable optty} `{!∀ x, Optionable (ty x) optty ot1 ot2} `{!∀ x1 x2, TCEq (ty x1).(ty_layout) (ty x2).(ty_layout)} : ROptionable (tyexists ty) optty ot1 ot2 := {|
    ropt_opt x := {| opt_pre v1 v2 := opt_pre (ty x) v1 v2 |}
  |}.
  Next Obligation.
    move => ?????????. rewrite /rmovable/=/ty_layout/ty_own_val. apply opt_alt_sz.
  Qed.
  Next Obligation.
    move => ?????????. rewrite /rmovable/=/ty_layout/ty_own_val. apply opt_bin_op.
  Qed.

  Global Instance optionable_agree_tyexists (ty2 : A → type) ty1 `{!∀ x, OptionableAgree (ty2 x) ty1} : OptionableAgree (tyexists ty2) ty1.
  Proof. done. Qed.

  (* TODO: Also have a version without refinement? *)
  Global Instance strip_guarded_tyexists E1 E2 (ty : A → type) ty' β `{!∀ y, StripGuarded β E1 E2 (ty y) (ty' y)}:
    StripGuarded β E1 E2 (tyexists ty) (tyexists ty').
  Proof.
    iIntros (l E HE1 HE2). iDestruct 1 as (x) "Hs". iExists x.
    rewrite !tyexists_eq. by iDestruct (strip_guarded with "Hs") as "$".
  Qed.
End tyexist.
