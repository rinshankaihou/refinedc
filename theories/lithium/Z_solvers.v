From refinedc.lithium Require Import base.
From Coq.btauto Require Import Btauto.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

Create HintDb simplify_bool_eq_db discriminated.

Hint Rewrite
  Bool.andb_false_r
  Bool.andb_true_r
  Bool.andb_false_l
  Bool.andb_true_l
  Bool.orb_false_r
  Bool.orb_true_r
  Bool.orb_false_l
  Bool.orb_true_l
  Bool.xorb_false_r
  Bool.xorb_true_r
  Bool.xorb_false_l
  Bool.xorb_true_l
  : simplify_bool_eq_db.

Ltac simplify_bool_eq := autorewrite with simplify_bool_eq_db.

Create HintDb simplify_index_db discriminated.

Hint Rewrite
  Z.sub_add
  Z.add_simpl_r
  : simplify_index_db.

Local Ltac simplify_index := autorewrite with simplify_index_db.

Lemma Z_bits_1_0 k :
  k = 0 → Z.testbit 1 k = true.
Proof. naive_solver. Qed.

Lemma Z_bits_1_above k :
  0 < k → Z.testbit 1 k = false.
Proof.
  intros. rewrite Z.bits_above_log2 //=.
Qed.

Create HintDb rewrite_bits_db discriminated.

Hint Rewrite
  (* 0 *)
  Z.bits_0
  (* 1 *)
  Z_bits_1_0
  Z_bits_1_above
  (* -1 *)
  Z.bits_m1
  (* bitwise *)
  Z.land_spec
  Z.lor_spec
  Z.lxor_spec
  Z.shiftl_spec
  Z.shiftr_spec
  Z.lnot_spec
  Z.ldiff_spec
  (* Z.ones *)
  Z.ones_spec_high
  Z.ones_spec_low
  (* Z.testbit, Z.setbit *)
  Z.testbit_neg_r
  Z.setbit_eq
  Z.setbit_neq
  (* out-of-bound index *)
  Z.bits_above_log2
  using lia : rewrite_bits_db.

Local Ltac rewrite_bits := rewrite_strat (repeat (topdown (hints rewrite_bits_db))).

Ltac rewrite_testbit := repeat (simplify_bool_eq || simplify_index || rewrite_bits).

Local Ltac compare_cases cst i :=
  tryif (first [assert (cst ≤ i) by lia | assert (i < cst) by lia])
  then fail
  else (let C := fresh "C" in
        assert (i < cst ∨ cst ≤ i) as C by lia;
        ring_simplify i in C;
        destruct C as [C | C]).

Local Ltac solve_or_split_step :=
  rewrite_testbit;
  try solve [f_equal; (reflexivity || lia)];
  match goal with
  | |- context [Z.testbit _ ?i] => compare_cases 0 i
  | |- context [Z.testbit (Z.ones ?sz) ?i] => compare_cases sz i
  end.

Ltac bitblast :=
  apply Z.bits_inj'; intros ?i ?Hi;
  repeat solve_or_split_step;
  rewrite_testbit;
  try btauto.

(** tests **)

Goal ∀ x a k, 
  Z.land x (Z.land (Z.ones k) (Z.ones k) ≪ a) =
  Z.land (Z.land (x ≫ a) (Z.ones k)) (Z.ones k) ≪ a.
  by intros; bitblast. Abort.

Goal ∀ i,
  1 ≪ i = Z.land (Z.ones 1) (Z.ones 1) ≪ i.
  by intros; bitblast. Abort.

Goal ∀ N k,
  0 ≤ k ≤ N → Z.ones N ≫ (N - k) = Z.ones k.
  by intros; bitblast. Abort.
