From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

Remove Hints find_in_context_type_val_P_own_singleton_inst : typeclass_instances.

Section instances.
  Context  `{!typeG Σ}.

  Global Instance simpl_to_NULL_val_of_loc (l : loc) : SimplAndRel (=) NULL (l) (λ T, False).
  Proof. split; naive_solver. Qed.

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

  Lemma simplify_hyp_place_combine_offset l β n ty T:
    ((l +ₗ n) ◁ₗ{β} ty -∗ T) -∗ simplify_hyp ((l.1, l.2 + n) ◁ₗ{β} ty) T.
  Proof. iIntros "HT". iApply "HT". Qed.
  Global Instance simplify_hyp_place_combine_offset_inst l β n ty:
    SimplifyHypPlace (l.1, l.2 + n) β ty (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_combine_offset l β n ty T).

  Lemma simplify_goal_place_combine_offset l β n ty T:
    T ((l +ₗ n) ◁ₗ{β} ty) -∗ simplify_goal ((l.1, l.2 + n) ◁ₗ{β} ty) T.
  Proof. iIntros "HT". iExists _. eauto with iFrame. Qed.
  Global Instance simplify_goal_place_combine_offset_inst l β n ty:
    SimplifyGoalPlace (l.1, l.2 + n) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_combine_offset l β n ty T).

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
End instances.

Typeclasses Opaque FindLocInBounds.
