From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

Section instances.
  Context  `{!typeG Σ}.

  Lemma simplify_goal_place_shift_loc_0nat_times l n β ty T:
    T (l ◁ₗ{β} ty) -∗ simplify_goal ((l +ₗ 0%nat * n) ◁ₗ{β} ty) T.
  Proof. iIntros "HT". assert (0%nat * n = 0) as -> by lia. rewrite shift_loc_0. iExists _. eauto with iFrame. Qed.
  Global Instance simplify_goal_place_shift_loc_0nat_times_inst l n β ty:
    SimplifyGoalPlace (l +ₗ 0%nat * n) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_shift_loc_0nat_times l n β ty T).

  Lemma simplify_goal_place_combine l β ty T:
    T (l ◁ₗ{β} ty) -∗ simplify_goal ((l.1, l.2) ◁ₗ{β} ty) T.
  Proof. iIntros "HT". assert ((l.1, l.2) = l) as -> by by destruct l. iExists _. eauto with iFrame. Qed.
  Global Instance simplify_goal_place_combine_inst l β ty:
    SimplifyGoalPlace (l.1, l.2) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_combine l β ty T).

  Lemma simplify_goal_place_combine_offset l β n ty T:
    T ((l +ₗ n) ◁ₗ{β} ty) -∗ simplify_goal ((l.1, l.2 + n) ◁ₗ{β} ty) T.
  Proof. iIntros "HT". iExists _. eauto with iFrame. Qed.
  Global Instance simplify_goal_place_combine_offset_inst l β n ty:
    SimplifyGoalPlace (l.1, l.2 + n) β ty (Some 0%N) | 100 :=
    λ T, i2p (simplify_goal_place_combine_offset l β n ty T).
End instances.
