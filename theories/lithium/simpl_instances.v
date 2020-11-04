From refinedc.lithium Require Import base simpl_classes infrastructure.

Local Open Scope Z_scope.

(* The followin impl is bad because it looses the name. *)
(* Global Instance simpl_exist_impl A P : SimplImpl true (@ex A P) (λ T, ∀ x, P x → T). *)
(* Proof. split; try naive_solver. intros ?[??]. eauto. Qed. *)
Global Instance simpl_exist_and A P : SimplAnd (@ex A P) (λ T, ∃ x, P x ∧ T).
Proof. split. naive_solver. intros [[??]?]. eauto. Qed.
Global Instance simpl_and_and (P1 P2 : Prop):
  SimplAnd (P1 ∧ P2) (λ T, P1 ∧ P2 ∧ T).
Proof. split; naive_solver. Qed.
Global Instance simpl_and_impl (P1 P2 : Prop):
  SimplImpl true (P1 ∧ P2) (λ T, P1 → P2 → T).
Proof. split; naive_solver. Qed.
Global Instance simpl_or_false1 P1 P2 `{!CanSolve (¬ P2)}:
  SimplBoth (P1 ∨ P2) (P1).
Proof. unfold CanSolve in *. split; naive_solver. Qed.
Global Instance simpl_or_false2 P1 P2 `{!CanSolve (¬ P1)}:
  SimplBoth (P1 ∨ P2) (P2).
Proof. unfold CanSolve in *. split; naive_solver. Qed.
Global Instance simpl_shelve_hint P:
  SimplImpl true (shelve_hint P) (λ T, P → T).
Proof. split; naive_solver. Qed.

Global Instance simpl_eq_pair A B (x1 x2 : A) (y1 y2 : B):
  SimplAnd ((x1, y1) = (x2, y2)) (λ T, x1 = x2 ∧ y1 = y2 ∧ T).
Proof. split; naive_solver. Qed.

Global Instance simple_protected_neq_empty A `{!EqDecision A} `{!Countable A} (p : gset A) `{!IsProtected p} :
  SimplAnd (p ≠ ∅) (λ T, shelve_hint (p ≠ ∅) ∧ T).
Proof. split; naive_solver. Qed.
Global Instance simple_protected_multiset_neq_empty A `{!EqDecision A} `{!Countable A} (p : gmultiset A) `{!IsProtected p} :
  SimplAnd (p ≠ ∅) (λ T, shelve_hint (p ≠ ∅) ∧ T).
Proof. split; naive_solver. Qed.

Global Instance simpl_to_cons_None A (l : list A) : SimplBothRel (=) (maybe2 cons l) None (l = nil).
Proof. split; destruct l; naive_solver. Qed.
Global Instance simpl_to_cons_Some A (l : list A) x : SimplBothRel (=) (maybe2 cons l) (Some x) (l = x.1::x.2).
Proof. split; destruct l, x; naive_solver. Qed.

Global Instance simpl_gt_0_neg n : SimplBoth (¬ (0 < n))%nat (n = 0%nat).
Proof. split; destruct n; naive_solver lia. Qed.

(* We want to do this for hyps (it allows simplification to take place), but not in the goal (as it might lead to evars which we cannot instantiate) *)
Global Instance simpl_gt_0_impl n : SimplImpl true (0 < n)%nat (λ T, (∃ n', n = S n') → T).
Proof. split; destruct n; naive_solver lia. Qed.
Global Instance simpl_gt_0_and n : SimplBoth (0 < S n)%nat True.
Proof. split; naive_solver lia. Qed.

Global Instance simpl_bool_decide_true P `{!Decision P} : SimplBothRel (=) (bool_decide P) true P.
Proof. split; case_bool_decide; naive_solver. Qed.
Global Instance simpl_bool_decide_false P `{!Decision P} : SimplBothRel (=) (bool_decide P) false (¬P).
Proof. split; case_bool_decide; naive_solver. Qed.
Global Instance simpl_bool_decide_eq P1 P2 `{!Decision P1} `{!Decision P2} : SimplBothRel (=) (bool_decide P1) (bool_decide P2) (P1 ↔ P2).
Proof. split; repeat case_bool_decide; naive_solver. Qed.

Global Instance simpl_if_bool_decide_true P x y `{!Decision P} `{!CanSolve P} : SimplBoth (if bool_decide P then x else y) x.
Proof. unfold CanSolve in *. by rewrite bool_decide_true. Qed.
Global Instance simpl_if_bool_decide_false P x y `{!Decision P} `{!CanSolve (¬ P)} : SimplBoth (if bool_decide P then x else y) y.
Proof. unfold CanSolve in *. by rewrite bool_decide_false. Qed.

Global Instance simpl_Is_true_true b : SimplBoth (Is_true b) (b = true).
Proof. split; destruct b; naive_solver. Qed.
Global Instance simpl_Is_true_false b : SimplBoth (¬ Is_true b) (b = false).
Proof. split; destruct b; naive_solver. Qed.

Global Instance simpl_gt_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} : SimplBoth (n1 > n2 * n1) (n2 = 0%nat).
Proof. unfold CanSolve in *; split; destruct n2; naive_solver lia. Qed.
Global Instance simpl_ge_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} : SimplBoth (n1 >= n2 * n1) (n2 = 0 ∨ n2 = 1)%nat.
Proof. unfold CanSolve in *; split; destruct n2 as [|[]]; naive_solver lia. Qed.
Global Instance simpl_gt_neq_0_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} : SimplBoth (¬ n1 > n2 * n1) (n2 > 0)%nat.
Proof. unfold CanSolve in *; split; destruct n2; try naive_solver lia. Qed.
Global Instance simpl_ge_neq_0_both (n1 n2 : nat) `{!CanSolve (n1 ≠ 0)%nat} : SimplBoth (¬ n1 >= n2 * n1) (n2 > 1)%nat.
Proof. unfold CanSolve in *; split; destruct n2 as [|[]]; naive_solver lia. Qed.
Global Instance simpl_mult_0 n m : SimplBothRel (=) (n * m) (0) (n = 0 ∨ m = 0).
Proof. split; destruct n, m; naive_solver lia. Qed.

Global Instance simpl_mult_neq_0 n m : SimplBoth (n * m ≠ 0) (n ≠ 0 ∧ m ≠ 0).
Proof. split; destruct n, m; naive_solver lia. Qed.
Global Instance simpl_mult_le z1 z2:
  SimplBoth (0 ≤ z1 * z2) ((0 ≤ z1 ∧ 0 ≤ z2) ∨ (z1 ≤ 0 ∧ z2 ≤ 0)).
Proof. split; destruct z1, z2; naive_solver lia. Qed.

Global Instance simpl_divides_and a b `{!CanSolve (a ≠ 0 ∧ b `mod` a = 0)}:
  SimplAnd (a | b) (λ T, T).
Proof. revert select (CanSolve _) => -[?]. rewrite Z.mod_divide //. split; naive_solver. Qed.

(* TODO: this rule is quite specialized. Can we compose it from less specialized rules?*)
Global Instance simpl_divides_impl_nat a b `{!CanSolve (0 < a)}:
  SimplImpl true (a | Z.of_nat b) (λ T, ∀ n : nat, (b = n * Z.to_nat a)%nat → T).
Proof.
  unfold CanSolve in *. rewrite /Z.divide. split.
  - move => HT [x Hx]. apply: (HT (Z.to_nat x)).
    rewrite -Z2Nat.inj_mul; try lia.
  - move => HT n ?. apply HT. eexists n. lia.
Qed.

Global Instance simpl_is_power_of_two_mult n1 n2 :
  SimplBoth (is_power_of_two (n1 * n2)) (is_power_of_two n1 ∧ is_power_of_two n2).
Proof. by apply is_power_of_two_mult. Qed.

(* TODO: This instance is quite specific and for mpool. *)
Global Instance simpl_forall_eq_plus n:
  SimplBoth (∀ x, x = n + x)%nat (n = 0)%nat.
Proof. unfold SimplBoth. split; last naive_solver lia. move => H. rewrite (H 0%nat). lia. Qed.

Global Instance simpl_n_mul_m_minus n m k `{!CanSolve (m ≠ 0)} : SimplBothRel (=) (n * m - m) (k * m) (n-1 = k).
Proof. unfold CanSolve in *. split; last naive_solver lia. move => ?. apply (Z.mul_cancel_r _ _ m) => //. lia. Qed.
(* TODO: unify these two instances *)
Global Instance simpl_n_mul_m_minus_nat n m k `{!CanSolve (m ≠ 0)%nat} : SimplBothRel (=) (n * m - m)%nat (k * m)%nat (n-1 = k)%nat.
Proof.
  unfold CanSolve in *. split.
  - move => ?. apply (Nat.mul_cancel_r _ _ m) => //. rewrite Nat.mul_sub_distr_r. lia.
  - move => <-. rewrite Nat.mul_sub_distr_r. lia.
Qed.
Global Instance simpl_cancel_mult_nat n1 n2 m `{!CanSolve (m ≠ 0)%nat}:
  SimplBothRel (=) (n1 * m)%nat (n2 * m)%nat (n1 = n2)%nat.
Proof. unfold SimplBothRel. unfold CanSolve in *. by rewrite Nat.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_le n1 n2 m `{!CanSolve (0 < m)}:
  SimplBothRel (≤) (n1 * m) (n2 * m) (n1 ≤ n2).
Proof. unfold SimplBothRel. unfold CanSolve in *. by rewrite -Z.mul_le_mono_pos_r. Qed.
Global Instance simpl_cancel_mult_eq n1 n2 m `{!CanSolve (0 ≠ m)}:
  SimplBothRel (=) (n1 * m) (n2 * m) (n1 = n2).
Proof. unfold SimplBothRel. unfold CanSolve in *. by rewrite Z.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_neq n1 n2 m `{!CanSolve (0 ≠ m)}:
  SimplBoth (n1 * m ≠ n2 * m) (n1 ≠ n2).
Proof. unfold SimplBothRel. unfold CanSolve in *. split; by rewrite Z.mul_cancel_r. Qed.
Global Instance simpl_cancel_mult_nat_Z n1 n2 m `{!CanSolve (m ≠ 0)%nat}:
  SimplBothRel (=) (n1 * m) (n2 * m)%nat (n1 = n2).
Proof. unfold SimplBothRel. unfold CanSolve in *. rewrite Nat2Z.inj_mul Z.mul_cancel_r; lia. Qed.
Global Instance simpl_Zsub_to_nat (n m : nat) `{!CanSolve (n > 0)} : SimplBothRel (=) (n - 1) m ((n-1) = m)%nat.
Proof. unfold CanSolve in *. split; naive_solver lia. Qed.
Global Instance simpl_Zadd_to_nat (n m : nat) : SimplBothRel (=) (n + 1) m ((n+1) = m)%nat.
Proof. unfold CanSolve in *. split; naive_solver lia. Qed.

Global Instance simpl_n_add_sub_n_nat n m k : SimplBothRel (=) (n + m - n)%nat (k)%nat (m = k)%nat.
Proof. split; naive_solver lia. Qed.

Global Instance simpl_nat_sub_0 (n m : nat) : SimplBothRel (=) (m - 0)%nat n (n = m).
Proof. split; naive_solver lia. Qed.

(* TODO: add a more general impl? *)
Global Instance simpl_eq_0 (n : nat) : SimplBothRel (=) (A := Z) n 0 (n = 0)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_1 (n : nat) : SimplBothRel (=) (A := Z) n 1 (n = 1)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_2 (n : nat) : SimplBothRel (=) (A := Z) n 2 (n = 2)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_3 (n : nat) : SimplBothRel (=) (A := Z) n 3 (n = 3)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_4 (n : nat) : SimplBothRel (=) (A := Z) n 4 (n = 4)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_5 (n : nat) : SimplBothRel (=) (A := Z) n 5 (n = 5)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_6 (n : nat) : SimplBothRel (=) (A := Z) n 6 (n = 6)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_7 (n : nat) : SimplBothRel (=) (A := Z) n 7 (n = 7)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_8 (n : nat) : SimplBothRel (=) (A := Z) n 8 (n = 8)%nat.
Proof. split; naive_solver lia. Qed.
Global Instance simpl_eq_9 (n : nat) : SimplBothRel (=) (A := Z) n 9 (n = 9)%nat.
Proof. split; naive_solver lia. Qed.

Global Instance simpl_eq_Ztonat (n m : nat) : SimplBothRel (=) (A := Z) n m (n = m).
Proof. split; naive_solver lia. Qed.

Global Instance simpl_Z_to_bool_0 (b : bool) : SimplBothRel (=) 0 (Z_of_bool b) (b = false).
Proof. split; destruct b; naive_solver. Qed.
Global Instance simpl_Z_to_bool_1 (b : bool) : SimplBothRel (=) 1 (Z_of_bool b) (b = true).
Proof. split; destruct b; naive_solver. Qed.

Global Instance simpl_add_eq_0 n m:
  SimplBothRel (=) (n + m)%nat (0)%nat (n = 0%nat ∧ m = 0%nat).
Proof. split; naive_solver lia. Qed.

Global Instance simpl_and_S n m `{!ContainsProtected n}:
  SimplAndRel (=) (S n) (m) (λ T, (m > 0)%nat ∧ n = pred m ∧ T).
Proof. split; destruct n; naive_solver lia. Qed.
Global Instance simpl_and_Z_of_nat n m `{!CanSolve (0 ≤ m)} `{!ContainsProtected n}:
  SimplAndRel (=) (Z.of_nat n) (m) (λ T, n = Z.to_nat m ∧ T).
Proof. unfold CanSolve in *. split; naive_solver lia. Qed.

Global Instance simpl_in_nil {A} (x : A):
  SimplBoth (x ∈ []) False.
Proof. split; set_solver. Qed.
Global Instance simpl_not_in_nil {A} (x : A):
  SimplBoth (x ∉ []) True.
Proof. split; set_solver. Qed.
Global Instance simpl_in_cons {A} (x : A) y ys:
  SimplBoth (x ∈ y :: ys) (x = y ∨ x ∈ ys).
Proof. split; set_solver. Qed.
Global Instance simpl_not_in_cons {A} (x : A) y ys:
  SimplBoth (x ∉ y :: ys) (x ≠ y ∧ x ∉ ys).
Proof. split; set_solver. Qed.

Global Instance simpl_length_0 {A} (l : list A):
  SimplBothRel (=) (length l) (0%nat) (l = []).
Proof. split; by destruct l. Qed.

Global Instance simpl_length_S {A} (l : list A) (n : nat):
  SimplAndRel (=) (length l) (S n) (λ T, (∃ hd tl, l = hd :: tl ∧ length tl = n) ∧ T).
Proof.
  split.
  - move => [[hd [tl [-> <-]]] HT] //.
  - move => [Hlen HT]. split => //. destruct l as [|hd tl] => //.
    eexists hd, tl. by inversion Hlen.
Qed.

Global Instance simpl_length_protected_add {A} (n m : nat) (p : list A) `{!ContainsProtected p} `{!CanSolve (m ≤ n)%nat} :
  SimplAndRel (=) (n) (length p + m)%nat (λ T, (n - m)%nat = length p ∧ T).
Proof.
  unfold CanSolve in *. split.
  - move => [Heq ?]. split => //. lia.
  - move => [-> P]. split => //. lia.
Qed.

Global Instance simpl_insert_list_subequiv {A} (l1 l2 : list A) j x1 `{!CanSolve (j < length l1)%nat} :
  SimplBothRel (=) (<[j:=x1]>l1) l2 (list_subequiv [j] l1 l2 ∧ l2 !! j = Some x1).
Proof. unfold CanSolve in *. split; rewrite list_insert_subequiv //; naive_solver. Qed.

Global Instance simpl_insert_subequiv {A} (l1 l2 : list A) j x1 ig `{!CanSolve (j < length l1)%nat}:
  SimplBothRel (list_subequiv ig) (<[j:=x1]>l1) l2 (if bool_decide (j ∈ ig) then list_subequiv ig l1 l2 else
                                      list_subequiv (j :: ig) l1 l2 ∧ l2 !! j = Some x1).
Proof.
  unfold CanSolve in *. unfold SimplBothRel.
  case_bool_decide; [rewrite subequiv_insert_in_l | rewrite subequiv_insert_ne_l ]; naive_solver.
Qed.

Lemma lookup_eq_app_r {A} (l1 l2 suffix : list A) (i : nat) :
  length l1 = length l2 →
  l1 !! i = l2 !! i ↔ (l1 ++ suffix) !! i = (l2 ++ suffix) !! i.
Proof.
  move => Hlen. destruct (l1 !! i) as [v|] eqn:HEq.
  + rewrite lookup_app_l; last by eapply lookup_lt_Some.
    rewrite lookup_app_l; first by rewrite -HEq.
    apply lookup_lt_Some in HEq. by rewrite -Hlen.
  + rewrite lookup_app_r; last by apply lookup_ge_None.
    apply lookup_ge_None in HEq. rewrite Hlen in HEq.
    apply lookup_ge_None in HEq. rewrite HEq.
    split => [_|]//. rewrite lookup_app_r; first by rewrite Hlen.
    by apply lookup_ge_None.
Qed.

Global Instance simpl_app_r_subequiv {A} (l1 l2 suffix : list A) ig :
  SimplBothRel (list_subequiv ig) (l1 ++ suffix) (l2 ++ suffix) (list_subequiv ig l1 l2).
Proof.
  rewrite /list_subequiv. split => H i; move: (H i) => [Hlen Hlookup].
  - rewrite app_length app_length in Hlen. split; first by lia.
    move => /Hlookup. apply lookup_eq_app_r. by lia.
  - split; first by rewrite app_length app_length Hlen.
    move => /Hlookup. apply lookup_eq_app_r. by lia.
Qed.

(* The other direction requires `{!Inj (=) (=) f}, but we cannot prove
it if f goes into type. Thus we use the AssumeInj typeclass such that
the user can mark functions which are morally injective, but one
cannot prove it. *)
Global Instance simpl_fmap_fmap_subequiv_Unsafe {A B} (l1 l2 : list A) ig (f : A → B) `{!AssumeInj (=) (=) f}:
  SimplAndUnsafe true (list_subequiv ig (f <$> l1) (f <$> l2)) (λ T, list_subequiv ig l1 l2 ∧ T).
Proof.
  move => ? [Hs ?]. split => // i. move: (Hs 0%nat) => [Hlen _].
  do 2 rewrite fmap_length. split => // ?. rewrite !list_lookup_fmap.
 f_equal. move: (Hs i) => [_ ?]. naive_solver.
Qed.

(* The other direction might not hold if ig contains indices which are
out of bounds, but we don't care about that. *)
Global Instance simpl_subequiv_protected {A} (l1 l2 : list A) ig `{!IsProtected l2}:
  SimplAndUnsafe true (list_subequiv ig l1 l2) (λ T,
    foldr (λ i f, (λ l', ∃ x, f (<[i:=x]> l'))) (λ l', l2 = l' ∧ T) ig l1).
Proof.
  unfold list_subequiv, IsProtected in * => T. elim: ig l1 l2.
  - move => ??/=. move => [??]. naive_solver.
  - move => i ig IH l1 l2/= [x /IH [Hi ?]]. split => // i'.
    move: (Hi i') => [<- Hlookup]. rewrite insert_length. split => //.
    move => Hi'. rewrite -Hlookup ?list_lookup_insert_ne; set_solver.
Qed.

Global Instance simpl_fmap_nil {A B} (l : list A) (f : A → B) : SimplBothRel (=) (f <$> l) [] (l = []).
Proof. split; destruct l; naive_solver. Qed.
Global Instance simpl_fmap_cons_and {A B} (l : list A) l2 (f : A → B):
  SimplAndRel (=) (f <$> l) (x :: l2) (λ T, ∃ x' l2', l = x' :: l2' ∧ f x' = x ∧ f <$> l2' = l2 ∧ T).
Proof. split; first naive_solver. intros [?%fmap_cons_inv ?]. naive_solver. Qed.
Global Instance simpl_fmap_cons_impl {A B} (l : list A) l2 (f : A → B):
  SimplImplRel (=) true (f <$> l) (x :: l2) (λ T, ∀ x' l2', l = x' :: l2' → f x' = x → f <$> l2' = l2 → T).
Proof. split; last naive_solver. intros ? ?%fmap_cons_inv. naive_solver. Qed.
Global Instance simpl_fmap_app_and {A B} (l : list A) l1 l2 (f : A → B):
  SimplAndRel (=) (f <$> l) (l1 ++ l2) (λ T, f <$> take (length l1) l = l1 ∧ f <$> drop (length l1) l = l2 ∧ T).
Proof.
  split.
  - move => [Hl1 [Hl2 ?]]; subst. split => //.
    rewrite -Hl1 -fmap_app fmap_length take_length_le ?take_drop //.
    rewrite -Hl1 fmap_length take_length. lia.
  - move => [/fmap_app_inv [? [? [? [? Hfmap]]]] ?]; subst.
    by rewrite fmap_length take_app drop_app.
Qed.
Global Instance simpl_fmap_assume_inj_Unsafe {A B} (l1 l2 : list A) (f : A → B) `{!AssumeInj (=) (=) f}:
  SimplAndUnsafe true (f <$> l1 = f <$> l2) (λ T, l1 = l2 ∧ T).
Proof. move => T [-> ?]. naive_solver. Qed.

Global Instance simpl_replicate_app_and {A} (l1 l2 : list A) x n:
  SimplAndRel (=) (replicate n x) (l1 ++ l2) (λ T, ∃ n', shelve_hint (n' ≤ n)%nat ∧ l1 = replicate n' x ∧ l2 = replicate (n - n') x ∧ T).
Proof.
  unfold shelve_hint. split.
  - move => [n'[?[?[??]]]]; subst. split => //.
    have ->: (n = n' + (n - n'))%nat by lia. rewrite replicate_plus. do 2 f_equal. lia.
  - move => [Hr ?].
    have Hn: (n = length l1 + length l2)%nat by rewrite -(replicate_length n x) -app_length Hr.
    move: Hr. rewrite Hn replicate_plus => /app_inj_1[|<- <-]. by rewrite replicate_length.
    exists (length l1). repeat split => //.
    + rewrite !replicate_length. lia.
    + rewrite !replicate_length. f_equal. lia.
Qed.

Global Instance simpl_replicate_eq_nil {A} (x : A) n :
  SimplBothRel (=) (replicate n x) [] (n = 0%nat).
Proof. by destruct n. Qed.

Global Instance simpl_replicate_cons {A} (l : list A) x x' n:
  SimplBothRel (=) (replicate n x) (x' :: l) ((n > 0)%nat ∧ x' = x ∧ l = replicate (pred n) x).
Proof. split; destruct n; naive_solver lia. Qed.

Global Instance simpl_replicate_lookup {A} (x x' : A) n m :
  SimplBothRel (=) (replicate n x !! m) (Some x') (x' = x ∧ (m < n)%nat).
Proof. by apply: lookup_replicate. Qed.

Global Instance simpl_replicate_eq {A} (x : A) n n' :
  SimplBothRel (=) (replicate n x) (replicate n' x) (n = n').
Proof.
  split; last naive_solver. elim: n n'; first by case.
  move => n IH []//= n' []. naive_solver.
Qed.

Global Instance simpl_replicate_elem_of {A} (x x' : A) n :
  SimplBoth (x' ∈ replicate n x) (x' = x ∧ (n ≠ 0)%nat).
Proof. unfold SimplBoth. by set_unfold. Qed.

Global Instance simpl_filter_nil {A} P `{!∀ x, Decision (P x)} (l : list A) :
  SimplBothRel (=) (filter P l) [] (∀ x, x ∈ l → ¬ P x).
Proof. unfold SimplBothRel. by rewrite filter_nil_inv. Qed.

Global Instance simpl_app_r_id {A} (l1 l2 : list A):
  SimplBothRel (=) l2 (l1 ++ l2) (l1 = []).
Proof.
  split.
  - move => H. assert (length (l1 ++ l2) = length l2) as Hlen by by rewrite -H.
    rewrite app_length in Hlen. assert (length l1 = 0%nat) by lia. by destruct l1.
  - by naive_solver.
Qed.

Global Instance simpl_app_l_id {A} (l1 l2 : list A):
  SimplBothRel (=) l1 (l1 ++ l2) (l2 = []).
Proof.
  split.
  - move => H. assert (length (l1 ++ l2) = length l1) as Hlen by by rewrite -H.
    rewrite app_length in Hlen. assert (length l2 = 0%nat) by lia. by destruct l2.
  - move => ->. by rewrite -app_nil_end.
Qed.

(* TODO: make something more general *)
Global Instance simpl_cons_app_eq {A} (l1 l2 l3 : list A) x:
  SimplBothRel (=) (x :: l1 ++ l2) (l3 ++ l2) (x :: l1 = l3).
Proof. split; try naive_solver. move => ?. by apply: app_inv_tail. Qed.


Global Instance simpl_lookup_app {A} (l1 l2 : list A) i x:
  SimplBothRel (=) ((l1 ++ l2) !! i) (Some x)
               (if bool_decide (i < length l1)%nat then l1 !! i = Some x else l2 !! (i - length l1)%nat = Some x).
Proof.
  unfold SimplBothRel. case_bool_decide.
  - by rewrite lookup_app_l.
  - rewrite lookup_app_r //. lia.
Qed.

Global Instance simpl_rev_nil {A} (l : list A):
  SimplBothRel (=) (rev l) [] (l = []).
Proof.
  split.
  - move => H. destruct l; first done. simpl in H. by destruct (rev l).
  - move => ->. done.
Qed.

Global Instance simpl_lookup_drop {A} (l : list A) n i x :
  SimplBothRel (=) (drop n l !! i) (Some x) (l !! (n + i)%nat = Some x).
Proof. by rewrite lookup_drop. Qed.

Global Instance simpl_fmap_lookup_and {A B} (l : list A) i (f : A → B) x:
  SimplAndRel (=) ((f <$> l) !! i) (Some x) (λ T, ∃ y : A, x = f y ∧ l !! i = Some y ∧ T).
Proof.
  split.
  - move => [y [-> [Hl ?]]]. rewrite list_lookup_fmap Hl. naive_solver.
  - move => [Hf ?]. have := list_lookup_fmap_inv _ _ _ _ Hf. naive_solver.
Qed.
Global Instance simpl_fmap_lookup_impl {A B} (l : list A) i (f : A → B) x:
  SimplImplRel (=) true ((f <$> l) !! i) (Some x) (λ T, ∀ y : A, x = f y → l !! i = Some y → T).
Proof.
  split.
  - move => Hf /(list_lookup_fmap_inv _ _ _ _)?. naive_solver.
  - move => HT y ? Hl; subst. apply HT. by rewrite list_lookup_fmap Hl.
Qed.
Global Instance simpl_lookup_insert_eq {A} (l : list A) i j x x' `{!CanSolve (i = j)}:
  SimplBothRel (=) (<[i := x']> l !! j) (Some x) (x = x' ∧ (j < length l)%nat).
Proof.
  unfold SimplBothRel, CanSolve in *; subst.
  rewrite list_lookup_insert_Some. naive_solver.
Qed.
Global Instance simpl_lookup_insert_neq {A} (l : list A) i j x x' `{!CanSolve (i ≠ j)}:
  SimplBothRel (=) (<[i := x']> l !! j) (Some x) (l !! j = Some x).
Proof.
  unfold SimplBothRel, CanSolve in *; subst.
  rewrite list_lookup_insert_Some. naive_solver.
Qed.

Global Instance simpl_learn_insert_some_len_impl {A} l i (x : A) :
  (* The false is important here as we learn additional information,
  but don't want to get stuck in an endless loop. *)
  SimplImpl false (l !! i = Some x) (λ T, l !! i = Some x → (i < length l)%nat → T) | 100.
Proof. split; last naive_solver. move => HT ?. apply HT => //. by apply: lookup_lt_Some. Qed.

Global Instance simpl_is_Some_unfold {A} (o : option A):
  SimplBoth (is_Some o) (∃ x, o = Some x) | 100.
Proof. split; naive_solver. Qed.

Global Instance simpl_Some {A} o (x x' : A) `{!FastDone (o = Some x)}:
  SimplBothRel (=) (o) (Some x') (x = x') | 1.
Proof. unfold FastDone in *; subst. split; naive_solver. Qed.

Global Instance simpl_both_fmap_Some A f (o : option A) (x : A): SimplBothRel (=) (f <$> o) (Some x) (∃ x', o = Some  x' ∧ x = f x').
Proof. unfold SimplBothRel. rewrite fmap_Some. naive_solver. Qed.

Global Instance simpl_both_rotate_lookup_Some A b l i (x : A): SimplBothRel (=) (rotate b l !! i) (Some x) (l !! rotate_nat_add b i (length l) = Some x ∧ (i < length l)%nat).
Proof. unfold SimplBothRel. by rewrite lookup_rotate_r_Some. Qed.

(* Unsafe because the other direction does not hold if base >= len.
  But one should not use rotate nat in this case.
   TODO: use CanSolve when it is able to prove base < len for slot_for_key_ref key len *)
Global Instance simpl_rotate_nat_add_0_Unsafe base offset len:
  SimplAndUnsafe true (base = rotate_nat_add base offset len) (λ T, (base < len)%nat ∧ offset = 0%nat ∧ T).
Proof. move => T [? [-> ?]]. rewrite rotate_nat_add_0 //. Qed.

Global Instance simpl_rotate_nat_add_next_Unsafe (base offset1 offset2 len : nat) `{!CanSolve (0 < len)%nat}:
  SimplAndUnsafe true ((rotate_nat_add base offset1 len + 1) `rem` len = rotate_nat_add base offset2 len) (λ T, offset2 = S offset1 ∧ T).
Proof.
  unfold CanSolve in * => ? -[-> ?]. split => //. rewrite rotate_nat_add_S // Nat2Z_inj_mod.
  rewrite Z.rem_mod_nonneg //=; lia.
Qed.
