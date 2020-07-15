From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section wand.
  Context `{!typeG Σ}.

  Program Definition wand_ex {A} (P : A → iProp Σ) (ty : A → type) : type := {|
    ty_own β l := match β return _ with
                  | Own => ∀ x, P x -∗ l ◁ₗ (ty x)
                  | Shr => True
                  end
  |}%I.
  Next Obligation. by iIntros (??????) "?". Qed.

  Context {A : Type}. Implicit Types (P : A → iProp Σ).

  Lemma subsume_wand l P1 P2 ty1 ty2 T:
    (* The trick is that we prove the wand at the very end so it can
    use all leftover resources. This only works if there is at most
    one wand per block (but this is enough for iterating over linked
    lists). *)
    T ∗ (∀ x, P2 x -∗ ∃ y, P1 y ∗ (l ◁ₗ ty1 y -∗ l ◁ₗ ty2 x ∗ True)) -∗
    subsume (l ◁ₗ wand_ex P1 ty1) (l ◁ₗ wand_ex P2 ty2) T.
  Proof.
    iIntros "($&Hwand) Hwand2" (x) "HP2". iDestruct ("Hwand" with "HP2") as (y) "[HP1 Hty]".
    iDestruct ("Hwand2" with "HP1") as "Hty1". iDestruct ("Hty" with "Hty1") as "[$ _]".
  Qed.
  Global Instance subsume_wand_inst l P1 P2 ty1 ty2:
    SubsumePlace l Own (wand_ex P1 ty1)%I (wand_ex P2 ty2)%I :=
    λ T, i2p (subsume_wand l P1 P2 ty1 ty2 T).

  Lemma simplify_hyp_resolve_wand l (P : A → _) ty T:
    (∃ x, P x ∗ (l ◁ₗ ty x -∗ T)) -∗
    simplify_hyp (l ◁ₗ wand_ex P ty) T.
  Proof. iDestruct 1 as (x) "[HP HT]". iIntros "Hwand". iApply "HT". by iApply "Hwand". Qed.
   (* must be before [simplify_goal_place_refine_r] *)
  Global Instance simplify_hyp_resolve_wand_inst l P ty :
    SimplifyHypPlace l Own (wand_ex P ty) (Some 9%N) :=
    λ T, i2p (simplify_hyp_resolve_wand l P ty T).

  Lemma simplify_goal_wand_eq l (ty : A → type) T:
    T True -∗
    simplify_goal (l ◁ₗ wand_ex (λ x, l ◁ₗ (ty x)) ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "_" (x) "$". Qed.
  Global Instance simplify_goal_wand_eq_inst l ty:
    SimplifyGoalPlace l Own (wand_ex (λ x, l ◁ₗ (ty x)) ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_wand_eq l ty T).

  (* TODO: make this more general, maybe with a SimpleSubsume
  judgement, which does not have a continutation?*)
  Lemma simplify_goal_wand_eq_ref l ty (x1 x2 : A → _) T:
    T ⌜∀ x, x1 x = x2 x⌝ -∗
    simplify_goal (l ◁ₗ wand_ex (λ x, l ◁ₗ (x1 x) @ ty) (λ x, (x2 x) @ ty)) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros (Heq x) "?". by rewrite Heq. Qed.
  Global Instance simplify_goal_wand_eq_ref_inst l ty x1 x2:
    SimplifyGoalPlace l Own (wand_ex (λ x, l ◁ₗ (x1 x) @ ty) (λ x, (x2 x) @ ty))%I (Some 0%N) :=
    λ T, i2p (simplify_goal_wand_eq_ref l ty x1 x2 T).

End wand.
Notation wand P ty := (wand_ex (A:=unit) (λ _, P) (λ _, ty)).
