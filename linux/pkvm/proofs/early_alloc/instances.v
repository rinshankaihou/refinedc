From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(*** Demonstration of FindHypEqual ***)
(* Instance simpl_loc_offset_0_times (l : loc) (n : Z): *)
(*   SimplLoc (l +ₗ 0%nat * n) l. *)
(* Proof. assert (0%nat * n = 0) as -> by lia. by rewrite shift_loc_0. Qed. *)

(* TODO: move this to own.v or somewhere in the automation folder *)
Inductive FICLocSemantic : Set :=.
Global Instance find_in_context_type_loc_semantic_inst `{!typeG Σ} l :
  FindInContext (FindLoc l) 2%nat FICLocSemantic :=
  λ T, i2p (find_in_context_type_loc_id l T).

(* TODO: move this to somewhere in the automation folder *)
Lemma tac_solve_loc_eq `{!typeG Σ} l1 β1 ty1 l2 β2 ty2:
  l1 = l2 →
  FindHypEqual FICLocSemantic (l1 ◁ₗ{β1} ty1) (l2 ◁ₗ{β2} ty2) (l1 ◁ₗ{β2} ty2).
Proof. by move => ->. Qed.

(* TODO: move this to somewhere in the automation folder and implement
it properly. *)
Ltac solve_loc_eq :=
  rewrite ?shift_loc_0; done.

(* TODO: move this to somewhere in the automation folder *)
Hint Extern 10 (FindHypEqual FICLocSemantic (_ ◁ₗ{_} _) (_ ◁ₗ{_} _) _) =>
  (notypeclasses refine (tac_solve_loc_eq _ _ _ _ _ _ _); solve_loc_eq) : typeclass_instances.

(*** Simplification of locations ***)

Class SimplLoc (l1 l2 : loc) : Prop := simpl_loc : l1 = l2.

Instance simpl_loc_eta (l : loc):
  SimplLoc (l.1, l.2) l.
Proof. by destruct l. Qed.

Instance simpl_loc_eta_with_offset (l : loc) (n : Z):
  SimplLoc (l.1, l.2 + n) (l +ₗ n).
Proof. by destruct l. Qed.

Instance simpl_loc_shift_loc_assoc (l : loc) (n1 n2 : Z):
  SimplLoc (l +ₗ n1 +ₗ n2) (l +ₗ (n1 + n2)).
Proof. by rewrite shift_loc_assoc. Qed.

Instance simpl_loc_offset_add_assoc id p n1 n2:
  SimplLoc (id, p + n1 + n2) (id, p + (n1 + n2)).
Proof. by rewrite Z.add_assoc. Qed.

(* The following instances are probably over-specialized. *)
Instance simpl_loc_extra1 l n i j:
  SimplLoc (l +ₗ (n + (i + j)%nat)) (l +ₗ (n + i + j)).
Proof. f_equal. lia. Qed.

Instance simpl_loc_extra2 l n i:
  SimplLoc (l +ₗ (n * PAGE_SIZE + ly_size (PAGES i))) (l +ₗ (n + i) * PAGE_SIZE).
Proof. rewrite Z.mul_add_distr_r. repeat f_equal. rewrite /PAGES /ly_size /PAGE_SIZE /=. lia. Qed.

Instance simpl_loc_extra3 l n i:
  SimplLoc (l +ₗ (n * PAGE_SIZE + i ≪ 12)) (l +ₗ (n + i) * PAGE_SIZE).
Proof. rewrite Z.mul_add_distr_r. repeat f_equal. rewrite Z.shiftl_mul_pow2 //. Qed.

Instance simpl_loc_extra4 l n1 n2:
  SimplLoc (l +ₗ (n1 + 0%nat) * n2) (l +ₗ (n1 * n2)).
Proof. f_equal. lia. Qed.

Instance simpl_loc_extra5 l n1 n2 n3 n4:
  SimplLoc (l +ₗ (n1 + (n2 + n3)%nat) * n4) (l +ₗ (n1 + n2 + n3) * n4).
Proof. f_equal. lia. Qed.

(*** Things about PAGES ***)

Lemma ly_size_PAGES i : ly_size (PAGES i) = (i * Z.to_nat PAGE_SIZE)%nat.
Proof. by rewrite /PAGES /ly_with_align /ly_size. Qed.

Lemma ly_offset_PAGES n m:
  (ly_offset (PAGES n) (ly_size (PAGES m))) = PAGES (n - m).
Proof.
  rewrite ly_size_PAGES /ly_offset /PAGES /ly_with_align /ly_size /PAGE_SIZE /=.
  f_equal; first lia. rewrite min_l // /factor2 /factor2' /=. case_match => //=.
  assert (p = Pos.of_nat m * (2 ^ 12))%positive as ->. { simpl. lia. }
  rewrite Pos_factor2_mult Pos_factor2_pow. lia.
Qed.

Global Instance simpl_ly_size_page_le i j:
  SimplBothRel (≤)%nat (PAGES i).(ly_size) (PAGES j).(ly_size) (i ≤ j)%nat.
Proof. rewrite /PAGES /ly_with_align /ly_size /PAGE_SIZE /=. split; lia. Qed.

Global Instance simpl_ly_size_page_eq i j:
  SimplBothRel (=) (PAGES i).(ly_size) (PAGES j).(ly_size) (i = j).
Proof. rewrite !ly_size_PAGES /PAGE_SIZE. split; lia. Qed.

Global Instance simpl_extra1 k m n:
  SimplBoth (k = ly_size (ly_offset (PAGES n) (ly_size (PAGES m)))) (k = ly_size (PAGES (n - m))).
Proof. by rewrite ly_offset_PAGES. Qed.

Global Instance simpl_extra2 k m n:
  SimplBoth (ly_size (ly_offset (PAGES n) (ly_size (PAGES m))) = k) (ly_size (PAGES (n - m)) = k).
Proof. by rewrite ly_offset_PAGES. Qed.

Section instances.
  Context  `{!typeG Σ}.

  Global Instance simpl_to_NULL_val_of_loc (l : loc) : SimplAndRel (=) NULL (l) (λ T, False).
  Proof. split; naive_solver. Qed.

  (*** location normalization rules *)
  Lemma simplify_goal_place_simpl_loc l1 l2 β ty `{!SimplLoc l1 l2} T:
    T (l2 ◁ₗ{β} ty) -∗ simplify_goal (l1 ◁ₗ{β} ty) T.
  Proof. revert select (SimplLoc _ _) => ->. iIntros "?". iExists _. eauto with iFrame. Qed.
  Global Instance simplify_goal_place_simpl_loc_inst l1 l2 β ty `{!SimplLoc l1 l2}:
    SimplifyGoalPlace l1 β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_simpl_loc l1 l2 β ty T).

  Lemma simplify_hyp_place_simpl_loc l1 l2 β ty `{!SimplLoc l1 l2} T:
    (l2 ◁ₗ{β} ty -∗ T) -∗ simplify_hyp (l1 ◁ₗ{β} ty) T.
  Proof. revert select (SimplLoc _ _) => ->. eauto with iFrame. Qed.
  Global Instance simplify_hyp_place_simpl_loc_inst l1 l2 β ty `{!SimplLoc l1 l2}:
    SimplifyHypPlace l1 β ty (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_simpl_loc l1 l2 β ty T).

  Lemma simplify_hyp_place_PAGES_stuff l β n1 n2 ty T:
    ⌜0 ≤ n2⌝ ∗ ((l +ₗ ((n1 + n2) * PAGE_SIZE)) ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp ((l +ₗ (n1 * PAGE_SIZE + ly_size (PAGES (Z.to_nat n2)))) ◁ₗ{β} ty) T.
  Proof.
    iIntros "[% HT]".
    assert (Z.of_nat (ly_size (PAGES (Z.to_nat n2))) = n2 * PAGE_SIZE) as ->.
    { rewrite /PAGES /ly_size /ly_with_align /= Nat2Z.inj_mul Z2Nat.id //. }
    rewrite Z.mul_add_distr_r. done.
  Qed.
  Global Instance simplify_hyp_place_PAGES_stuff_inst l β n1 n2 ty:
    SimplifyHypPlace (l +ₗ (n1 * PAGE_SIZE + ly_size (PAGES (Z.to_nat n2)))) β ty (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_PAGES_stuff l β n1 n2 ty T).

  Lemma simplify_hyp_place_PAGES_stuff_minus_0 l β n1 n2 ty T:
    ⌜0 ≤ n2⌝ ∗((l +ₗ ((n1 + n2) * PAGE_SIZE)) ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp ((l +ₗ (n1 * PAGE_SIZE + ly_size (PAGES (Z.to_nat n2 - 0)))) ◁ₗ{β} ty) T.
  Proof.
    iIntros "[% HT]". assert (Z.to_nat n2 - 0 = Z.to_nat n2)%nat as -> by lia.
    assert (Z.of_nat (ly_size (PAGES (Z.to_nat n2))) = n2 * PAGE_SIZE) as ->.
    { rewrite /PAGES /ly_size /ly_with_align /= Nat2Z.inj_mul Z2Nat.id //. }
    rewrite Z.mul_add_distr_r. done.
  Qed.
  Global Instance simplify_hyp_place_PAGES_stuff_minus_0_inst l β n1 n2 ty:
    SimplifyHypPlace (l +ₗ (n1 * PAGE_SIZE + ly_size (PAGES (Z.to_nat n2 - 0)))) β ty (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_PAGES_stuff_minus_0 l β n1 n2 ty T).

  Lemma simplify_hyp_place_PAGE_SIZE_stuff_other l β n1 n2 ty T:
    ⌜0 ≤ n2⌝ ∗ ((l +ₗ (n1 + n2) * PAGE_SIZE) ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp ((l +ₗ (n1 + (Z.to_nat n2 - 0)%nat) * PAGE_SIZE) ◁ₗ{β} ty) T.
  Proof. iIntros "[% HT]". by rewrite Nat.sub_0_r Z2Nat.id. Qed.
  Global Instance simplify_hyp_place_PAGE_SIZE_stuff_other_inst l β n1 n2 ty:
    SimplifyHyp ((l +ₗ (n1 + (Z.to_nat n2 - 0)%nat) * PAGE_SIZE) ◁ₗ{β} ty) (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_PAGE_SIZE_stuff_other l β n1 n2 ty T).

  Lemma simplify_hyp_loc_in_bounds_ptr_in_range l (n : nat) T:
    (⌜min_alloc_start ≤ l.2 ∧ l.2 + n ≤ max_alloc_end⌝ -∗ loc_in_bounds l n -∗ T) -∗
    simplify_hyp (loc_in_bounds l n) T.
  Proof.
    iIntros "HT Hlib".
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    by iApply "HT".
  Qed.
  (* FIXME limit the application in a cleaner way. *)
  Global Instance simplify_hyp_loc_in_bounds_ptr_in_range_inst l n `{!TCUnless (FastDone (min_alloc_start ≤ l.2))}:
    SimplifyHyp (loc_in_bounds l n) (Some 0%N) :=
    λ T, i2p (simplify_hyp_loc_in_bounds_ptr_in_range l n T).
End instances.

Typeclasses Opaque PAGES.
Global Opaque PAGES.
