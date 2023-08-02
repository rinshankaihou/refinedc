From iris.bi Require Import bi.
From lithium Require Export base.
From lithium Require Import hooks.

(** This file contains the pure definitions that are used by the
automation. *)

(** * [li_prod]: Products for marking existential quantifiers *)
(** li_prod should be linear and always terminated by unit for uniformity *)
#[projections(primitive)]
Record li_prod (A B : Type) : Type := li_pair { li_fst : A; li_snd : B }.
Add Printing Constructor li_prod.
Global Arguments li_pair {_ _} _ _.
Global Arguments li_fst {_ _} _.
Global Arguments li_snd {_ _} _.

Global Instance li_prod_inhabited A B `{!Inhabited A} `{!Inhabited B} : Inhabited (li_prod A B) :=
  populate (li_pair inhabitant inhabitant).

Notation "p '.1ₗ'" := (li_fst p) (at level 2, left associativity, format "p '.1ₗ'") : stdpp_scope.
Notation "p '.nextₗ'" := (li_snd p) (at level 2, left associativity, format "p '.nextₗ'") : stdpp_scope.
Notation "p '.2ₗ'" := (li_fst (li_snd p))
   (at level 2, left associativity, format "p '.2ₗ'") : stdpp_scope.
Notation "p '.3ₗ'" := (li_fst (li_snd (li_snd p)))
   (at level 2, left associativity, format "p '.3ₗ'") : stdpp_scope.
Notation "p '.4ₗ'" := (li_fst (li_snd (li_snd (li_snd p))))
   (at level 2, left associativity, format "p '.4ₗ'") : stdpp_scope.
Notation "p '.5ₗ'" := (li_fst (li_snd (li_snd (li_snd (li_snd p)))))
   (at level 2, left associativity, format "p '.5ₗ'") : stdpp_scope.
Notation "p '.6ₗ'" := (li_fst (li_snd (li_snd (li_snd (li_snd (li_snd p))))))
   (at level 2, left associativity, format "p '.6ₗ'") : stdpp_scope.
Notation "p '.7ₗ'" := (li_fst (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd p)))))))
   (at level 2, left associativity, format "p '.7ₗ'") : stdpp_scope.
Notation "p '.8ₗ'" := (li_fst (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd p))))))))
   (at level 2, left associativity, format "p '.8ₗ'") : stdpp_scope.
Notation "p '.9ₗ'" := (li_fst (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd (li_snd p)))))))))
   (at level 2, left associativity, format "p '.9ₗ'") : stdpp_scope.
(* Note that these notation are left associative, but normal products are right associative. *)
(* TODO: figure out right level, * is at level 40, but that is left associative *)
Notation "A *ₗ B" := (li_prod A B) (at level 39, right associativity) : type_scope.
(* TODO always add tt at the end? Then the notation probably needs to
start with ₗ to avoid conflicts with the usual pair notation. *)
Notation "( x , .. , y , z )ₗ" := (li_pair x .. (li_pair y z) .. )
   (at level 0, x at level 200, y at level 200, z at level 200, format "( x ,  .. ,  y ,  z )ₗ")  : stdpp_scope.

Notation "∃ₗ x .. y , P" :=
  (@bi_exist _ (_ *ₗ _) (λ x, .. (@bi_exist _ (_ *ₗ _) (λ y, P%I)) ..))
    (at level 200, x binder, P at level 200, right associativity, only parsing)
 : bi_scope.

Ltac red_li_prod := cbv [li_fst li_snd].

(** * [IsEx] and [ContainsEx] *)
Class ContainsEx {A} (x : A) : Set := {}.
Class IsEx {A} (x : A) : Set := {}.
Global Hint Extern 0 (ContainsEx ?x) =>
  (lazymatch x with | context [li_fst _] => constructor end) : typeclass_instances.
Global Hint Extern 0 (IsEx (li_fst _) ) => (constructor) : typeclass_instances.

(** * [CanSolve] *)
(** Exposes the general purpose solver in [can_solve_hook] (see
 hooks.v) as the [can_solve] tactic and via the [CanSolve] typeclass. *)
Tactic Notation "can_solve" := can_solve_hook.
Class CanSolve (P : Prop) : Prop := can_solve_proof: P.
Global Hint Extern 10 (CanSolve ?P) => (change P; can_solve) : typeclass_instances.
