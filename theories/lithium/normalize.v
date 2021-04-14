From refinedc.lithium Require Import base tactics_extend infrastructure.

(** * First version of normalization based on [autorewrite] *)
Create HintDb lithium_rewrite discriminated.

Ltac normalize_autorewrite :=
  autorewrite with lithium_rewrite; exact: eq_refl.

Hint Rewrite @drop_0 @take_ge using can_solve_tac : lithium_rewrite.
Hint Rewrite @take_app_le @drop_app_ge using can_solve_tac : lithium_rewrite.
Hint Rewrite @insert_length @app_length @fmap_length @rotate_length @replicate_length @drop_length : lithium_rewrite.
Hint Rewrite <- @fmap_take @fmap_drop : lithium_rewrite.
Hint Rewrite @list_insert_fold : lithium_rewrite.
Hint Rewrite @list_insert_insert : lithium_rewrite.
Hint Rewrite @drop_drop : lithium_rewrite.
Hint Rewrite @tail_replicate @take_replicate @drop_replicate : lithium_rewrite.
Hint Rewrite <- @app_assoc @cons_middle : lithium_rewrite.
Hint Rewrite @app_nil_r @rev_involutive : lithium_rewrite.
Hint Rewrite <- @list_fmap_insert : lithium_rewrite.
Hint Rewrite <- minus_n_O plus_n_O minus_n_n : lithium_rewrite.
Hint Rewrite Nat2Z.id : lithium_rewrite.
Hint Rewrite Z2Nat.inj_mul Z2Nat.inj_sub Z2Nat.id using can_solve_tac : lithium_rewrite.
Hint Rewrite Nat.succ_pred_pos using can_solve_tac : lithium_rewrite.
Hint Rewrite Nat.add_assoc Nat.min_id : lithium_rewrite.
Hint Rewrite Z.quot_mul using can_solve_tac : lithium_rewrite.
Hint Rewrite <-Nat.mul_sub_distr_r Z.mul_add_distr_r Z.mul_sub_distr_r : lithium_rewrite.
Hint Rewrite @bool_decide_eq_x_x_true @if_bool_decide_eq_branches : lithium_rewrite.
Hint Rewrite keep_factor2_is_power_of_two keep_factor2_min_eq using can_solve_tac : lithium_rewrite.
Hint Rewrite keep_factor2_min_1 keep_factor2_twice : lithium_rewrite.

Local Definition lookup_insert_gmap A K `{Countable K} := lookup_insert (M := gmap K) (A := A).
Hint Rewrite lookup_insert_gmap : lithium_rewrite.

(** * Second version of normalization based on typeclasses *)
Class NormalizeWalk {A} (progress : bool) (a b : A) : Prop := normalize_walk: a = b.
Class Normalize {A} (progress : bool) (a b : A) : Prop := normalize: a = b.
Hint Mode NormalizeWalk + - + - : typeclass_instances.
Hint Mode Normalize + - + - : typeclass_instances.
Global Instance normalize_walk_protected A (x : A) :
  NormalizeWalk false (protected x) (protected x) | 10.
Proof. done. Qed.
(* TODO: This does not go under binders *)
Lemma normalize_walk_app A B (f f' : A → B) x x' r p1 p2 p3
      `{!NormalizeWalk p1 f f'}
      `{!NormalizeWalk p2 x x'} `{!TCEq (p1 || p2) true}
      `{!Normalize p3 (f' x') r}:
  NormalizeWalk true (f x) r.
Proof. unfold NormalizeWalk, Normalize in *. naive_solver. Qed.
Hint Extern 50 (NormalizeWalk _ (?f ?x) _) => class_apply normalize_walk_app : typeclass_instances.
Global Instance normalize_walk_end_progress A (x x' : A) `{!Normalize true x x'} :
  NormalizeWalk true x x' | 100.
Proof. done. Qed.
Global Instance normalize_walk_end A (x : A) :
  NormalizeWalk false x x | 101.
Proof. done. Qed.
Global Instance normalize_end A (x : A): Normalize false x x | 100.
Proof. done. Qed.

Lemma normalize_fmap_length A B (f : A → B) l r p `{!Normalize p (length l) r} :
  Normalize true (length (f <$> l)) r.
Proof. by rewrite fmap_length. Qed.
Hint Extern 5 (Normalize _ (length (_ <$> _)) _) => class_apply normalize_fmap_length : typeclass_instances.
Lemma normalize_insert_length A i (x : A) l r p `{!Normalize p (length l) r} :
  Normalize true (length (<[i:=x]> l)) r.
Proof. by rewrite insert_length. Qed.
Hint Extern 5 (Normalize _ (length (<[_:=_]> _)) _) => class_apply normalize_insert_length : typeclass_instances.
Lemma normalize_app_length A (l1 l2 : list A) r1 r2 r3 p1 p2 p3
       `{!Normalize p1 (length l1) r1} `{!Normalize p2 (length l2) r2} `{!Normalize p3 (r1 + r2)%nat r3}:
  Normalize true (length (l1 ++ l2)) r3.
Proof. unfold Normalize in *; subst. by rewrite app_length. Qed.
Hint Extern 5 (Normalize _ (length (_ ++ _)) _) => class_apply normalize_app_length : typeclass_instances.
Lemma normalize_app_assoc A (l1 l2 l3 : list A) r1 r2 p1 p2
       `{!Normalize p1 (l2 ++ l3) r1} `{!Normalize p2 (l1 ++ r1) r2}:
  Normalize true ((l1 ++ l2) ++ l3) r2.
Proof. unfold Normalize in *; subst. by rewrite -app_assoc. Qed.
Hint Extern 5 (Normalize _ (((_ ++ _) ++ _)) _) => class_apply normalize_app_assoc : typeclass_instances.
Lemma normalize_cons_middle A x (l1 l2 : list A) r1 r2 p1 p2
       `{!Normalize p1 (x :: l2) r1} `{!Normalize p2 (l1 ++ r1) r2}:
  Normalize true (l1 ++ [x] ++ l2) r2.
Proof. unfold Normalize in *; subst. by rewrite -cons_middle. Qed.
(* The hint extern is especially imporant for this lemma as otherwise
tc search loops on goal of form l ++ [_]. *)
Hint Extern 5 (Normalize _ (_ ++ [_] ++ _) _) => class_apply normalize_cons_middle : typeclass_instances.
Lemma normalize_app_nil_r A (l : list A):
  Normalize true (l ++ []) l.
Proof. unfold Normalize in *; subst. by rewrite app_nil_r. Qed.
Hint Extern 5 (Normalize _ (_ ++ []) _) => class_apply normalize_app_nil_r : typeclass_instances.
Lemma normalize_rev_involutive A (l : list A):
  Normalize true (rev (rev l)) l.
Proof. unfold Normalize in *; subst. by rewrite rev_involutive. Qed.
Hint Extern 5 (Normalize _ (rev (rev _)) _) => class_apply normalize_rev_involutive : typeclass_instances.
Lemma normalize_minus_n_O n:
  Normalize true (n - 0)%nat n.
Proof. unfold Normalize in *; subst. by rewrite -minus_n_O. Qed.
Hint Extern 5 (Normalize _ (_ - 0)%nat _) => class_apply normalize_minus_n_O : typeclass_instances.
Lemma normalize_rotate_length A n (l : list A) r p `{!Normalize p (length l) r} :
  Normalize true (length (rotate n l)) r.
Proof. by rewrite rotate_length. Qed.
Hint Extern 5 (Normalize _ (length (rotate _ _)) _) => class_apply normalize_rotate_length : typeclass_instances.
Lemma normalize_replicate_length A n (l : list A) :
  Normalize true (length (replicate n l)) n.
Proof. by rewrite replicate_length. Qed.
Hint Extern 5 (Normalize _ (length (replicate _ _)) _) => class_apply normalize_replicate_length : typeclass_instances.

Ltac normalize_tc :=
  first [
      lazymatch goal with
      | |- ?a = ?b => change_no_check (NormalizeWalk true a b); solve [refine _]
      end
    | exact: eq_refl].