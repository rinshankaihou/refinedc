From refinedc.lang Require Import base.
Open Scope Z_scope.

(** Representation of a standard (8-bit) byte. *)

Definition bits_per_byte : Z := 8.

Definition byte_modulus : Z :=
  Eval cbv in 2 ^ bits_per_byte.

Record byte :=
  Byte {
    byte_val : Z;
    byte_constr : -1 < byte_val < byte_modulus;
  }.

Program Definition byte0 : byte := {| byte_val := 0; |}.
Next Obligation. done. Qed.

Instance byte_eq_dec : EqDecision byte.
Proof.
  move => [b1 H1] [b2 H2]. destruct (decide (b1 = b2)) as [->|].
  - left. assert (H1 = H2) as ->; [|done]. apply proof_irrel.
  - right. naive_solver.
Qed.
