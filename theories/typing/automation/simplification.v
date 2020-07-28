(** This file collects simplification instances specific to RefinedC *)
From refinedc.typing Require Import type.
From refinedc.lithium Require Import tactics.

(** * layout *)
Global Instance simpl_layout_eq ly1 ly2 : SimplAndRel (=) ly1 ly2 (λ T, ly1.(ly_size) = ly2.(ly_size) ∧ ly_align ly1 = ly_align ly2 ∧ T).
Proof. split; rewrite -ly_align_log_ly_align_eq_iff; destruct ly1,ly2; naive_solver. Qed.

Global Instance simpl_layout_leq ly1 ly2 : SimplBoth (ly1 ⊑ ly2) (ly1.(ly_size) ≤ ly2.(ly_size) ∧ ly_align ly1 ≤ ly_align ly2)%nat.
Proof. split; rewrite /ly_align -Nat.pow_le_mono_r_iff //; lia. Qed.

Global Instance simpl_is_power_of_two_align ly :
  SimplAnd (is_power_of_two (ly_align ly)) (λ T, T).
Proof. split => ?; last naive_solver. split => //. by eexists _. Qed.

(** * aligned_to *)
Global Instance simpl_aligned_to_add1 l (n : nat) : SimplBoth ((l +ₗ n) `aligned_to` n) (l `aligned_to` n).
Proof. rewrite -{1}(Z.mul_1_l n). apply aligned_to_add. Qed.
Global Instance simpl_aligned_to_add l m (n : nat) : SimplBoth ((l +ₗ m * n) `aligned_to` n) (l `aligned_to` n).
Proof. apply aligned_to_add. Qed.

Global Instance simpl_learn_aligned_to_mult l o n1 n2 `{!CanSolve (l `aligned_to` n2)} `{!CanSolve (0 ≤ o)} :
  SimplImpl false ((l +ₗ o) `aligned_to` (n1 * n2)) (λ T, (l +ₗ o) `aligned_to` (n1 * n2) → ∀ o', o = (o' * n2)%nat → T) | 100.
Proof.
  unfold CanSolve in *. split; last naive_solver. move => HT Halign.
  feed destruct (aligned_to_mult_eq l n1 n2 o) as [x ?] => //; subst. apply: (HT _ (Z.to_nat x)) => //.
  destruct x; lia.
Qed.

(** * location offset *)
Global Instance simpl_offset_inj l1 l2 sl n : SimplBothRel (=) (l1 at{sl}ₗ n) (l2 at{sl}ₗ n) (l1 = l2).
Proof. unfold GetMemberLoc. split; [apply shift_loc_inj1| naive_solver]. Qed.
