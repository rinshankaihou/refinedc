From refinedc.typing Require Export type.
From refinedc.typing Require Import programs singleton optional constrained exist.
Set Default Proof Using "Type".

Section tyfold.
  Context `{!typeG Σ}.

  Program Definition tyfold_type (tys : list (type → type)) (base : type) (ls : list loc) : type := {|
    ty_own β l := ⌜length ls = length tys⌝ ∗
            ([∗ list] i ↦ ty ∈ tys, ∃ l1 l2, ⌜(l::ls) !! i = Some l1⌝ ∗ ⌜ls !! i = Some l2⌝ ∗
           l1 ◁ₗ{β} ty (singleton_place l2)) ∗ (default l (last ls)) ◁ₗ{β} base
  |}%I.
  Next Obligation.
    iIntros (tys base ls l E ?). iDestruct 1 as (Hlen) "(Htys&Hb)".
    iMod (ty_share with "Hb") as "$" => //. iSplitR => //.
    iInduction (tys) as [|ty tys] "IH" forall (l ls Hlen) => //.
    destruct ls as [|l' ls] => //=. move: Hlen => /= [Hlen].
    iDestruct "Htys" as "[Hty Htys]". iDestruct "Hty" as (l1 l2 [=->] [=->]) "Hty".
    iMod (ty_share with "Hty") as "Hty" => //. iSplitL "Hty". 1: iExists _, _; by iFrame.
    by iApply "IH".
  Qed.
  Program Definition tyfold (tys : list (type → type)) (base : type) : rtype := {|
    rty_type := list loc;
    rty := tyfold_type tys base
  |}.

  Typeclasses Transparent own_constrained persistent_own_constraint.
  Lemma simplify_hyp_place_tyfold_optional l β ls tys b T:
    (l ◁ₗ{β} (maybe2 cons tys) @ optionalO (λ '(ty, tys), tyexists (λ l2, tyexists (λ ls2,
       constrained (
       own_constrained (tyown_constraint l2 (ls2 @ tyfold tys b)) (ty (singleton_place l2))) (⌜ls = l2::ls2⌝)))) b -∗ T) -∗
    simplify_hyp (l◁ₗ{β} ls @ tyfold tys b) T.
  Proof.
    iIntros "HT Hl". iApply "HT". iDestruct "Hl" as (Hlen) "[Htys Hb]".
    destruct tys as [|ty tys], ls as [ |l' ls] => //=.
    iDestruct "Htys" as "[H1 Hty2]". iDestruct "H1" as (l1 l2 ??) "H1". simplify_eq.
    iExists l2. rewrite tyexists_eq. iExists ls. rewrite tyexists_eq. iSplit => //.
    iSplitL "H1" => //=. rewrite /tyown_constraint. iSplit => //. iFrame.
    iStopProof. f_equiv. destruct ls =>//. by apply default_last_cons.
  Qed.
  Global Instance simplify_hyp_place_tyfold_optional_inst l β ls tys b:
    SimplifyHypPlace l β (ls @ tyfold tys b) (Some 50%N) :=
    λ T, i2p (simplify_hyp_place_tyfold_optional l β ls tys b T).

  Lemma simplify_goal_place_tyfold_nil l β ls b T:
    T (⌜ls = []⌝ ∗ l ◁ₗ{β} b) -∗ simplify_goal (l◁ₗ{β} ls @ tyfold [] b) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "[-> Hl]". repeat iSplit => //. Qed.
  Global Instance simplify_goal_place_tyfold_nil_inst l β ls b:
    SimplifyGoalPlace l β (ls @ tyfold [] b) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_tyfold_nil l β ls b T).

  Lemma simplify_goal_place_tyfold_cons l β ls ty tys b T:
    T (∃ l2 ls2, ⌜ls = l2::ls2⌝ ∗ l ◁ₗ{β} (ty (singleton_place l2)) ∗ (l2 ◁ₗ{β} ls2 @ tyfold tys b)) -∗
      simplify_goal (l◁ₗ{β} ls @ tyfold (ty :: tys) b) T.
  Proof.
    iIntros "HT". iExists _. iFrame. iDestruct 1 as (l2 ls2 ->) "[Hl [% [Htys Hb]]]".
    iSplit => /=. by iPureIntro; f_equal. iFrame.
    iSplitR "Hb"; first by eauto with iFrame.
    iStopProof. f_equiv. destruct ls2 =>//. by apply default_last_cons.
  Qed.
  Global Instance simplify_goal_place_tyfold_cons_inst l β ls ty tys b:
    SimplifyGoalPlace l β (ls @ tyfold (ty :: tys) b) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_tyfold_cons l β ls ty tys b T).

  Lemma subsume_tyfold_eq l β ls1 ls2 tys b1 b2 T :
    (⌜ls1 = ls2⌝ ∗ subsume (default l (last ls1) ◁ₗ{β} b1) (default l (last ls1) ◁ₗ{β} b2) T) -∗
    subsume (l ◁ₗ{β} ls1 @ tyfold tys b1) (l ◁ₗ{β} ls2 @ tyfold tys b2) T.
  Proof. iIntros "[-> HT]". iDestruct 1 as (?) "[$ Hb]". by iDestruct ("HT" with "Hb") as "[$ $]". Qed.
  Global Instance subsume_tyfold_eq_inst l β ls1 ls2 tys b1 b2:
    Subsume (l ◁ₗ{β} ls1 @ tyfold tys b1)%I (l ◁ₗ{β} ls2 @ tyfold tys b2)%I :=
    λ T, i2p (subsume_tyfold_eq l β ls1 ls2 tys b1 b2 T ).

  Lemma subsume_tyfold_snoc A l β f ls1 ls2 tys (ty : A) b1 b2 T :
    (∃ l2, ⌜ls2 = ls1 ++ [l2]⌝ ∗ (default l (last ls1) ◁ₗ{β} b1 -∗
        default l (last ls1) ◁ₗ{β} f ty (singleton_place l2) ∗ l2 ◁ₗ{β} b2 ∗ T)) -∗
    subsume (l ◁ₗ{β} ls1 @ tyfold (f <$> tys) b1) (l ◁ₗ{β} ls2 @ tyfold (f <$> (tys ++ [ty])) b2) T.
  Proof.
    iDestruct 1 as (l2 ->) "Hd". iDestruct 1 as (Hlen) "(Htys&Hb)". rewrite fmap_app.
    iDestruct ("Hd" with "Hb") as "[Hb1 [Hb $]]". iSplit.
    { iPureIntro. by rewrite !app_length Hlen fmap_length. }
    rewrite last_snoc /=. iFrame. iSplitL "Htys" => /=.
    - iApply (big_sepL_mono with "Htys") => k y /(lookup_lt_Some _ _ _). rewrite -Hlen => Hl /=.
      rewrite ?app_comm_cons !lookup_app_l//=. lia.
    - iSplit => //. rewrite -plus_n_O !lookup_app_r -?Hlen -?minus_n_n /=; try lia.
      iExists _, _. iFrame. iSplit => //. iPureIntro. rewrite ?app_comm_cons lookup_app_l /=; try lia.
      by apply list_lookup_length_default_last.
  Qed.
  Global Instance subsume_tyfold_snoc_inst A l β f ls1 ls2 tys (ty : A) b1 b2:
    SubsumePlace l β (ls1 @ tyfold (f <$> tys) b1) (ls2 @ tyfold (f <$> (tys ++ [ty])) b2) :=
    λ T, i2p (subsume_tyfold_snoc A l β f ls1 ls2 tys ty b1 b2 T ).
End tyfold.
Typeclasses Opaque tyfold_type.
