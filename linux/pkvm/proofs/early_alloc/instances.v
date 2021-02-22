From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_spec.
Set Default Proof Using "Type".

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

Instance simpl_loc_offset_0_times (l : loc) (n : Z):
  SimplLoc (l +ₗ 0%nat * n) l.
Proof. assert (0%nat * n = 0) as -> by lia. by rewrite shift_loc_0. Qed.

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

(*** Things about PAGES ***)

Global Instance simpl_ly_size_page_le i j:
  SimplBothRel (≤)%nat (PAGES i).(ly_size) (PAGES j).(ly_size) (i ≤ j)%nat.
Proof. rewrite /PAGES /ly_with_align /ly_size /PAGE_SIZE /=. split; lia. Qed.

Lemma ly_size_PAGES i : ly_size (PAGES i) = (i * Z.to_nat PAGE_SIZE)%nat.
Proof. by rewrite /PAGES /ly_with_align /ly_size. Qed.

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

  Lemma type_cast_ptr_int_val (v : val) (p : loc) (n : nat) T:
    (⌜min_alloc_start ≤ p.2 ∧ p.2 + n ≤ max_alloc_end⌝ -∗
      v ◁ᵥ p @ ptr n -∗ T (i2v p.2 size_t) (t2mt (p.2 @ int uintptr_t))) -∗
    typed_un_op v (v ◁ᵥ p @ ptr n) (CastOp (IntOp uintptr_t)) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iDestruct "Hp" as "[-> #Hlib]".
    iDestruct (loc_in_bounds_in_range_uintptr_t with "Hlib") as %[? H]%val_of_int_is_some.
    iDestruct (loc_in_bounds_ptr_in_range with "Hlib") as %?.
    iDestruct ("HT" with "[] []") as "HT"; first done. { by iFrame "Hlib". }
    iApply wp_cast_ptr_int => //=; first by rewrite val_to_of_loc.
    rewrite /i2v H /=. iApply ("HΦ" with "[] [HT]"); last done. done.
  Qed.
  Global Instance type_cast_ptr_int_val_inst (v : val) (p : loc) n:
    TypedUnOp v (v ◁ᵥ p @ ptr n)%I (CastOp (IntOp uintptr_t)) PtrOp :=
    λ T, i2p (type_cast_ptr_int_val v p n T).

  Lemma subsume_own_ptr p l1 l2 ty n T:
    ⌜l1 = l2⌝ ∗ (l1 ◁ₗ ty -∗ loc_in_bounds l1 n ∗ T) -∗
    subsume (p ◁ₗ l1 @ &own ty)%I (p ◁ₗ l2 @ ptr n)%I T.
  Proof.
    iIntros "[-> HT] Hp".
    iDestruct (ty_aligned with "Hp") as %?.
    iDestruct (ty_deref with "Hp") as (v) "[Hp [-> Hl]]".
    iDestruct ("HT" with "Hl") as "[#Hlib $]".
    iFrame "Hp Hlib". done.
  Qed.
  Global Instance subsume_own_ptr_inst p l1 l2 ty n:
    Subsume (p ◁ₗ l1 @ &own ty)%I (p ◁ₗ l2 @ ptr n)%I :=
    λ T, i2p (subsume_own_ptr p l1 l2 ty n T).

  Global Instance intro_persistent_loc_in_bounds l n:
    IntroPersistent (loc_in_bounds l n) (loc_in_bounds l n).
  Proof. constructor. by iIntros "#H !>". Qed.

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

  Lemma ly_offset_PAGES n m:
    (ly_offset (PAGES n) (ly_size (PAGES m))) = PAGES (n - m).
  Proof.
    rewrite ly_size_PAGES /ly_offset /PAGES /ly_with_align /ly_size /PAGE_SIZE /=.
    f_equal; first lia. rewrite min_l // /factor2 /factor2' /=. case_match => //=.
    assert (p = Pos.of_nat m * (2 ^ 12))%positive as ->. { simpl. lia. }
    rewrite Pos_factor2_mult Pos_factor2_pow. lia.
  Qed.

  Lemma subsume_zeroed_zeroed_PAGES p n1 n2 (T : iProp Σ) `{!CanSolve (n1 ≤ n2)%nat}:
    ((p +ₗ ly_size (PAGES n2)) ◁ₗ zeroed (PAGES (n1 - n2)) -∗ T) -∗
    subsume (p ◁ₗ zeroed (PAGES n1))%I (p ◁ₗ zeroed (PAGES n2))%I T.
  Proof.
    revert select (CanSolve _) => Hle. unfold CanSolve in Hle.
    iIntros "HT Hp".
  Admitted.
  Global Instance subsume_zeroed_zeroed_PAGES_inst p n1 n2 `{!CanSolve (n1 ≤ n2)%nat}:
    Subsume (p ◁ₗ zeroed (PAGES n1))%I (p ◁ₗ zeroed (PAGES n2))%I :=
    λ T, i2p (subsume_zeroed_zeroed_PAGES p n1 n2 T).

  Lemma subsume_zeroed_zeroed_PAGES_lt p n1 n2 (T : iProp Σ) `{!CanSolve (n2 ≤ n1)%nat}:
    (p +ₗ ly_size (PAGES n1)) ◁ₗ zeroed (PAGES (n2 - n1)) ∗ T -∗
    subsume (p ◁ₗ zeroed (PAGES n1))%I (p ◁ₗ zeroed (PAGES n2))%I T.
  Admitted.
  Global Instance subsume_zeroed_zeroed_PAGES_lt_inst p n1 n2 `{!CanSolve (n2 ≤ n1)%nat}:
    Subsume (p ◁ₗ zeroed (PAGES n1))%I (p ◁ₗ zeroed (PAGES n2))%I :=
    λ T, i2p (subsume_zeroed_zeroed_PAGES_lt p n1 n2 T).
End instances.

Typeclasses Opaque FindLocInBounds.

Typeclasses Opaque PAGES.
Global Opaque PAGES.

(* Typeclasses Opaque PAGE_SIZE PAGE_SHIFT. *)
