(** General infrastructure *)
From refinedc.lithium Require Import base.

(** * [protected] *)
Definition protected_def {A} (a : A) : A := a.
Definition protected_aux {A} (a : A) : seal (@protected_def A a). by eexists. Qed.
Definition protected {A} (a : A) : A := (protected_aux a).(unseal).
Definition protected_eq {A} (a : A) : protected a = a := (protected_aux a).(seal_eq).

Class ContainsProtected {A} (x : A) : Set := contains_protected: ().
Class IsProtected {A} (x : A) : Set := is_protected: ().
Hint Extern 0 (ContainsProtected ?x) => (match x with | context [protected _] => exact: tt end) : typeclass_instances.
Hint Extern 0 (IsProtected (protected _) ) => (exact: tt) : typeclass_instances.

(** * [IsVar] *)
Class IsVar {A} (x : A) : Prop := is_var: True.
Hint Extern 0 (IsVar ?x) => (is_var x; exact: I) : typeclass_instances.

(** * [AssumeInj] *)
Class AssumeInj {A B} (R : relation A) (S : relation B) (f : A → B) : Prop := assume_inj : True.
Global Instance assume_inj_inj A B R S (f : A → B) `{!Inj R S f} : AssumeInj R S f.
Proof. done. Qed.

(** * Checking if a hyp exists *)
Ltac check_hyp_not_exists P :=
  assert_fails (assert (P) as _;[fast_done|]).
Class CheckHypNotExists (P : Prop) : Prop := check_hyp_not_exists : True.
Hint Extern 1 (CheckHypNotExists ?P) => (check_hyp_not_exists P; change True; fast_done) : typeclass_instances.

(** * Different ways of checking if a property holds  *)
(** ** [FastDone]
 Should be used if it is expected that the property shows up directly as a hypothesis. *)
Class FastDone (P : Prop) : Prop := fast_done_proof : P.
Hint Extern 1 (FastDone ?P) => (change P; fast_done) : typeclass_instances.

(** ** [CanSolve]
 Requires the user to provide a general purpose [can_solve_tac] (see tactics.v)
 which should try hard to solve this goal. *)
Class CanSolve (P : Prop) : Prop := can_solve: P.

(** * [shelve_hint] *)
Definition shelve_hint (P : Prop) : Prop := P.
Typeclasses Opaque shelve_hint.
Arguments shelve_hint : simpl never.
