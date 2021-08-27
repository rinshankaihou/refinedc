From refinedc.lang Require Import base int_type.
From refinedc.lithium Require Import Z_bitblast.

(* least significant 1-bit *)

Definition is_least_significant_one (k n : Z) : Prop :=
  Z.testbit n k = true ∧ ∀ i, 0 ≤ i < k → Z.testbit n i = false.

Definition Z_least_significant_one (n : Z) : Z :=
  if bool_decide (n = 0) then -1 else Z.log2 (Z.land n (-n)).

Lemma Z_least_significant_one_sound k n :
  0 ≤ k →
  is_least_significant_one k n →
  Z_least_significant_one n = k.
Proof.
  rewrite /is_least_significant_one /Z_least_significant_one => ? [Heq Hlt].
  case_bool_decide; first by
    subst; have ? := Z.bits_0 k; congruence.
  suff : Z.land n (- n) = 1 ≪ k.
  { move => ->. rewrite Z.shiftl_1_l Z.log2_pow2. all: lia. }
  apply Z.bits_inj' => i ?.
  rewrite Z.land_spec ?Z.shiftl_spec //.
  destruct (decide (i = k)) as [->|]; last destruct (decide (i < k)).
  - (* i = k *)
    have ? : n `mod` 2 ^ k = 0 by apply Z_mod_pow2_zero_iff.
    rewrite Z_bits_opp_z ?Heq ?Z_bits_1_0 //; lia.
  - (* i < k *)
    have ? : n `mod` 2 ^ i = 0.
    { apply Z_mod_pow2_zero_iff.
      2: intros; apply Hlt.
      all: lia. }
    rewrite Z_bits_opp_z ?Hlt ?Z.testbit_neg_r //; lia.
  - (* i > k *)
    have ? : n `mod` 2 ^ i ≠ 0.
    { move => /Z_mod_pow2_zero_iff He.
      have Hcontra : Z.testbit n k = false by apply He; lia.
      congruence. }
    rewrite Z_bits_opp_nz ?Z_bits_1_above //; [|lia..].
    by rewrite andb_negb_r.
Qed.
