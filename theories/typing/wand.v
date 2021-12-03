From refinedc.typing Require Export type.
From refinedc.typing Require Import programs.
Set Default Proof Using "Type".

Section wand.
  Context `{!typeG Σ}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_ex P (ty : A → type) : type := {|
    ty_own β l := match β return _ with
                  | Own => ∀ x, P x -∗ l ◁ₗ (ty x)
                  | Shr => True
                  end;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation. by iIntros (?????) "?". Qed.

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
Notation "wand< P , ty >" := (wand P ty)
  (only printing, format "'wand<' P ,  ty '>'") : printing_sugar.

Section wand_val.
  Context `{!typeG Σ}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_val_ex ly P (ty : A → type) : type := {|
    ty_has_op_type ot mt := ot = UntypedOp ly;
    ty_own β l :=
      ∃ v,  ⌜l `has_layout_loc` ly⌝ ∗ ⌜v `has_layout_val` ly⌝ ∗ l ↦[β] v ∗
        match β return _ with
        | Own => ∀ x, P x -∗ v ◁ᵥ (ty x)
        | Shr => True
        end;
     ty_own_val v := (⌜v `has_layout_val` ly⌝ ∗ ∀ x, P x -∗ v ◁ᵥ (ty x))%I;
  |}%I.
  Next Obligation.
    iIntros (??????) "H". iDestruct "H" as (v) "(Hly1&Hly2&Hl&_)".
    iMod (heap_mapsto_own_state_share with "Hl") as "Hl". eauto with iFrame.
  Qed.
  Next Obligation. iIntros (??????->) "Hl". iDestruct "Hl" as (?) "[$ _]". Qed.
  Next Obligation. iIntros (??????->) "[$ _]". Qed.
  Next Obligation. iIntros (??????->) "Hl". iDestruct "Hl" as (v) "(?&?&?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (?????? v ->) "??[??]". iExists v. iFrame. Qed.
  Next Obligation. iIntros (????????). apply mem_cast_compat_Untyped. by simplify_eq/=. Qed.

  Global Instance wand_val_loc_in_bounds P ly β (ty : A → type):
    LocInBounds (wand_val_ex ly P ty) β (ly_size ly).
  Proof.
    constructor. iIntros (l) "Hl". iDestruct "Hl" as (?) "(_&Hly&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "H".
    by iDestruct "Hly" as %->.
  Qed.

  Lemma subsume_wand_val v ly1 ly2 P1 P2 ty1 ty2 T:
    (* The trick is that we prove the wand at the very end so it can
    use all leftover resources. This only works if there is at most
    one wand per block (but this is enough for iterating over linked
    lists). *)
    ⌜ly1 = ly2⌝ ∗ T ∗ (∀ x, P2 x -∗ ∃ y, P1 y ∗ (v ◁ᵥ ty1 y -∗ v ◁ᵥ ty2 x ∗ True)) -∗
    subsume (v ◁ᵥ wand_val_ex ly1 P1 ty1) (v ◁ᵥ wand_val_ex ly2 P2 ty2) T.
  Proof.
    iIntros "(->&$&Hwand) ($&Hty1)" (x) "HP2".
    iDestruct ("Hwand" with "HP2") as (y) "[HP1 Hwand]".
    iDestruct ("Hty1" with "HP1") as "Hty1". iDestruct ("Hwand" with "Hty1") as "[$_]".
  Qed.
  Global Instance subsume_wand_val_inst v ly1 ly2 P1 P2 ty1 ty2:
    SubsumeVal v (wand_val_ex ly1 P1 ty1)%I (wand_val_ex ly2 P2 ty2)%I :=
    λ T, i2p (subsume_wand_val v ly1 ly2 P1 P2 ty1 ty2 T).

  Lemma simplify_hyp_resolve_wand_val v ly P ty T:
    (∃ x, P x ∗ (v ◁ᵥ ty x -∗ T)) -∗
    simplify_hyp (v ◁ᵥ wand_val_ex ly P ty) T.
  Proof.
    iDestruct 1 as (x) "[HP HT]". iIntros "[_ Hwand]".
    iApply "HT". by iApply "Hwand".
  Qed.
  (* must be before [simplify_goal_place_refine_r] *)
  Global Instance simplify_hyp_resolve_wand_val_inst v ly P ty:
    SimplifyHypVal v (wand_val_ex ly P ty) (Some 9%N) :=
    λ T, i2p (simplify_hyp_resolve_wand_val v ly P ty T).

  Lemma simplify_goal_wand_val_eq v ly (ty : A → type) T:
    ⌜v `has_layout_val` ly⌝ ∗ T True -∗
    simplify_goal (v ◁ᵥ wand_val_ex ly (λ x, v ◁ᵥ (ty x)) ty) T.
  Proof. iIntros "[??]". iExists _. iFrame. by eauto. Qed.
  Global Instance simplify_goal_wand_val_eq_inst v ly ty:
    SimplifyGoalVal v (wand_val_ex ly (λ x, v ◁ᵥ (ty x)) ty)%I (Some 0%N) :=
    λ T, i2p (simplify_goal_wand_val_eq v ly ty T).

  (* TODO: make this more general, maybe with a SimpleSubsume
  judgement, which does not have a continutation?*)
  Lemma simplify_goal_wand_val_eq_ref v ly ty (x1 x2 : A → _) T:
    ⌜v `has_layout_val` ly⌝ ∗ T ⌜∀ x, x1 x = x2 x⌝ -∗
    simplify_goal (v ◁ᵥ wand_val_ex ly (λ x, v ◁ᵥ (x1 x) @ ty) (λ x, (x2 x) @ ty)) T.
  Proof. iIntros "[??]". iExists _. iFrame. iIntros (Heq x) "?". by rewrite Heq. Qed.
  Global Instance simplify_goal_wand_val_eq_ref_inst v ly ty x1 x2:
    SimplifyGoalVal v (wand_val_ex ly (λ x, v ◁ᵥ (x1 x) @ ty) (λ x, (x2 x) @ ty))%I (Some 0%N) :=
    λ T, i2p (simplify_goal_wand_val_eq_ref v ly ty x1 x2 T).
End wand_val.
Notation wand_val ly P ty := (wand_val_ex (A:=unit) ly (λ _, P) (λ _, ty)).
Notation "wand_val< ly , P , ty >" := (wand_val ly P ty)
  (only printing, format "'wand_val<' ly ,  P ,  ty '>'") : printing_sugar.
