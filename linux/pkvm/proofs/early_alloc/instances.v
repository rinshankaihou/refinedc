From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

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

Lemma ly_size_ly_offset ly m:
  (ly_size (ly_offset ly m) = ly_size ly - m)%nat.
Proof. done. Qed.

Lemma ly_size_PAGES_sub n m:
  (ly_size (PAGES n) - ly_size (PAGES m) = ly_size (PAGES (n - m)))%nat.
Proof. rewrite !ly_size_PAGES. lia. Qed.

Typeclasses Opaque PAGES.
Global Opaque PAGES.

Hint Rewrite ly_size_ly_offset : refinedc_rewrite.
Hint Rewrite ly_size_PAGES_sub : refinedc_rewrite.
Hint Rewrite ly_size_PAGES : refinedc_rewrite.
Hint Rewrite ly_offset_PAGES : refinedc_rewrite.

Hint Rewrite ly_size_ly_offset : refinedc_loc_eq_rewrite.
Hint Rewrite ly_size_PAGES_sub : refinedc_loc_eq_rewrite.
Hint Rewrite ly_size_PAGES : refinedc_loc_eq_rewrite.
Hint Rewrite ly_offset_PAGES : refinedc_loc_eq_rewrite.

Global Instance simpl_to_NULL_val_of_loc (l : loc):
  SimplAndRel (=) NULL (l) (λ T, False).
Proof. split; naive_solver. Qed.

Section instances.
  Context `{!typeG Σ}.

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
