From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

(*** Simplification of locations ***)

Lemma ly_size_PAGES i : ly_size (PAGES i) = (i * Z.to_nat PAGE_SIZE)%nat.
Proof. by rewrite /PAGES /ly_with_align /ly_size. Qed.

Lemma ly_offset_PAGES n m:
  (ly_offset (PAGES n) (ly_size (PAGES m))) = PAGES (n - m).
Proof.
  rewrite ly_size_PAGES /ly_offset /PAGES /ly_with_align /ly_size /=.
  f_equal; first lia. rewrite min_l // /factor2 /factor2' /=. case_match => //=.
  assert (p = Pos.of_nat m * (2 ^ 12))%positive as ->. { simpl. lia. }
  rewrite Pos_factor2_mult Pos_factor2_pow. lia.
Qed.

Global Instance simpl_ly_size_page_le i j:
  SimplBothRel (≤)%nat (PAGES i).(ly_size) (PAGES j).(ly_size) (i ≤ j)%nat.
Proof. rewrite /PAGES /ly_with_align /ly_size /=. split; lia. Qed.

Global Instance simpl_ly_size_page_eq i j:
  SimplBothRel (=) (PAGES i).(ly_size) (PAGES j).(ly_size) (i = j).
Proof. rewrite !ly_size_PAGES. split; lia. Qed.

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
