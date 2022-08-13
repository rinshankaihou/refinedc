From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

(* TODO: These proofs could be cleaned up quite a bit. *)

Lemma Z_land_add_l a b n:
  0 ≤ n →
  a `mod` (1 ≪ n) = 0 →
  0 ≤ b < 1 ≪ n →
  Z.land (a + b) (1 ≪ n - 1) = b.
Proof.
  move => ?. rewrite Z.shiftl_1_l -Z.land_ones // Z.sub_1_r -Z.ones_equiv.
  move => /Z.bits_inj_iff' Ha [Hb' /Z.bounded_iff_bits_nonneg Hb].
  apply Z.bits_inj_iff' => n' ?. rewrite Z.land_spec Z.ones_spec //.
  case_bool_decide; rewrite ?andb_true_r ?andb_false_r.
  2: { symmetry. naive_solver lia. }
  rewrite Z.add_nocarry_lxor.
  - rewrite Z.lxor_spec.
    move: (Ha n'). rewrite Z.land_spec Z.ones_spec // Z.bits_0. case_bool_decide => //.
    rewrite andb_true_r => -> //=. by case_match.
  - apply Z.bits_inj_iff' => n'' ?. rewrite Z.land_spec Z.bits_0.
    destruct (decide (n ≤ n'')).
    + rewrite Hb ?andb_false_r //; lia.
    + move: (Ha n''). rewrite Z.land_spec Z.ones_spec // Z.bits_0. case_bool_decide; [|lia].
      by rewrite andb_true_r => ->.
Qed.

Lemma Z_land_add_lunot bits a b n:
  0 ≤ n ≤ bits →
  0 ≤ a < 1 ≪ bits →
  a `mod` (1 ≪ n) = 0 →
  0 ≤ b < 1 ≪ n →
  Z.land (a + b) (Z_lunot bits (1 ≪ n - 1)) = a.
Proof.
  move => [??]. rewrite !Z.shiftl_1_l -Z.land_ones // Z.sub_1_r -Z.ones_equiv.
  move => [? /Z.bounded_iff_bits_nonneg Ha] /Z.bits_inj_iff' Ha' [? /Z.bounded_iff_bits_nonneg Hb].
  apply Z.bits_inj_iff' => n' ?.
  rewrite Z.add_nocarry_lxor. 2: {
    apply Z.bits_inj_iff' => n'' ?. rewrite Z.land_spec Z.bits_0.
    destruct (decide (n ≤ n'')).
    + rewrite Hb ?andb_false_r //; lia.
    + move: (Ha' n''). rewrite Z.land_spec Z.ones_spec // Z.bits_0. case_bool_decide; [|lia].
      by rewrite andb_true_r => ->.
  }
  rewrite Z.land_spec Z.lxor_spec.
  destruct (decide (bits ≤ n')).
  { rewrite Ha //=; [|lia]. rewrite Hb//. lia. }
  rewrite Z_lunot_spec; [|lia]. rewrite Z.ones_spec //. case_bool_decide; rewrite ?andb_true_r ?andb_false_r.
  - move: (Ha' n'). rewrite Z.land_spec Z.ones_spec // Z.bits_0. case_bool_decide; [|lia].
    by rewrite andb_true_r => ->.
  - rewrite Hb //; [|lia] => /=. by rewrite xorb_false_r.
Qed.

Lemma Z_lor_land_not bits a b c n:
  0 ≤ n ≤ bits →
  0 ≤ a < 1 ≪ bits →
  a `mod` (1 ≪ n) = 0 →
  0 ≤ b < 1 ≪ n →
  0 ≤ c < 1 ≪ n →
  Z.lor (Z.land (a + b) (Z_lunot bits (1 ≪ n - 1))) c = a + c.
Proof.
  move => Hn Ha1 Ha2 Hb Hc.
  rewrite Z_land_add_lunot //.
  suff : Z.land a c = 0. { move => ?. by rewrite Z.add_nocarry_lxor ?Z.lxor_lor. }
  move: Hn Ha1 Ha2 Hc => [??]. rewrite !Z.shiftl_1_l -Z.land_ones//.
  move => [? /Z.bounded_iff_bits_nonneg Ha] /Z.bits_inj_iff' Ha' [? /Z.bounded_iff_bits_nonneg Hc].
  apply Z.bits_inj_iff' => n'' ?. rewrite Z.land_spec Z.bits_0.
  destruct (decide (n ≤ n'')).
  + rewrite Hc ?andb_false_r //; lia.
  + move: (Ha' n''). rewrite Z.land_spec Z.ones_spec // Z.bits_0. case_bool_decide; [|lia].
      by rewrite andb_true_r => ->.
Qed.
