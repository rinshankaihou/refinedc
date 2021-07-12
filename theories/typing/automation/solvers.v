From refinedc.typing Require Import type.
From refinedc.lithium Require Import tactics.
From refinedc.lithium Require Export solvers.

Lemma unfold_int_elem_of_it (z : Z) (it : int_type) :
  z ∈ it = (min_int it ≤ z ∧ z ≤ max_int it).
Proof. done. Qed.

Ltac unfold_common_defs :=
  unfold
  (* Unfold [aligned_to] and [Z.divide] as lia can work with the underlying multiplication. *)
    aligned_to, Z.divide,
  (* Unfold [addr] since [lia] may get stuck due to [addr]/[Z] mismatches. *)
    addr,
  (* Layout *)
    ly_size, ly_with_align, ly_align_log,
  (* Integer bounds *)
    max_int, min_int, int_half_modulus, int_modulus,
    bits_per_int, bytes_per_int,
  (* Address bounds *)
    max_alloc_end, min_alloc_start, bytes_per_addr,
  (* Other byte-level definitions *)
    bits_per_byte in *.

(** * [solve_goal] without cleaning of the context  *)
Ltac solve_goal_normalized_prepare_tac ::=
  try rewrite -> unfold_int_elem_of_it in *;
  unfold_common_defs; simpl in *;
  rewrite /ly_size/ly_align_log //=.

(** * Tactics for solving sideconditions in ..._spec.v files  *)
