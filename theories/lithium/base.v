From refinedc.lang Require Export base.
From iris.base_logic.lib Require Export iprop.
From iris.proofmode Require Export tactics.

Typeclasses Opaque list_subequiv is_Some.
(* This is necessary since otherwise keyed unification unfolds these definitions *)
Global Opaque rotate_nat_add rotate_nat_sub.

(** What follows are random things where is is not clear where to put them*)
