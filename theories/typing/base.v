From refinedc.lang Require Export proofmode.
From refinedc.lithium Require Export lithium.

Create HintDb refinedc_typing.

Ltac solve_typing :=
  (typeclasses eauto with refinedc_typing typeclass_instances core).

Hint Constructors Forall Forall2 elem_of_list : refinedc_typing.
Hint Resolve submseteq_cons submseteq_inserts_l submseteq_inserts_r
  : refinedc_typing.

Hint Extern 1 (@eq nat _ (Z.to_nat _)) =>
  (etrans; [symmetry; exact: Nat2Z.id | reflexivity]) : refinedc_typing.
Hint Extern 1 (@eq nat (Z.to_nat _) _) =>
  (etrans; [exact: Nat2Z.id | reflexivity]) : refinedc_typing.

Hint Resolve <- elem_of_app : refinedc_typing.

(* done is there to handle equalities with constants *)
Hint Extern 100 (_ ≤ _) => simpl; first [done|lia] : refinedc_typing.
Hint Extern 100 (@eq Z _ _) => simpl; first [done|lia] : refinedc_typing.
Hint Extern 100 (@eq nat _ _) => simpl; first [done|lia] : refinedc_typing.

Class CoPsetFact (P : Prop) : Prop := copset_fact : P.
(* clear for performance reasons as there can be many hypothesis and they should not be needed for the goals which occur *)
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Hint Extern 1 (CoPsetFact ?P) => (change P; clear; eauto using coPset_disjoint_empty_r, coPset_disjoint_empty_r with solve_ndisj) : typeclass_instances.
