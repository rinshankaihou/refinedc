From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section immovable.
  Context `{!typeG Σ}.

  Program Definition immovable (ty : loc → type) : type := {|
    ty_own q l := (ty l).(ty_own) q l
  |}.
  Next Obligation. iIntros (????). by iApply ty_share. Qed.

  Global Instance immovable_ne n : Proper (pointwise_relation loc (dist n) ==> (dist n)) immovable.
  Proof. solve_type_proper. Qed.
  Global Instance immovable_proper : Proper (pointwise_relation loc (≡) ==> (≡)) immovable.
  Proof. solve_type_proper. Qed.

  Lemma simplify_hyp_place_immovable l β ty T:
    (l ◁ₗ{β} ty l -∗ T) -∗ simplify_hyp (l◁ₗ{β} immovable ty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Global Instance simplify_hyp_place_immovable_inst l β ty :
    SimplifyHypPlace l β (immovable ty) (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_immovable l β ty T).

  Lemma simplify_goal_place_immovable l β ty T:
    T (l ◁ₗ{β} ty l) -∗ simplify_goal (l◁ₗ{β} immovable ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "$". Qed.
  Global Instance simplify_goal_place_immovable_inst l β ty :
    SimplifyGoalPlace l β (immovable ty) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_immovable l β ty T).
End immovable.

Typeclasses Opaque immovable.
