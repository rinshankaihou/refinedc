From caesium Require Import builtins_specs.
From refinedc.typing Require Import typing.
Set Default Proof Using "Type".

Lemma clearbit_equiv bm priority :
  min_int u64 ≤ bm →
  bm ≤ max_int u64 →
  Z.land bm (Z_lunot (bits_per_int u64) (1 ≪ priority)) =
    Z.clearbit bm priority.
Proof.
  move => GE LE.
  bitblast as n. symmetry.
  apply (Z_bounded_iff_bits_nonneg' n) => //=.
  split; [done|].
  eapply Z.le_lt_trans; [exact LE|].
  eapply Z.lt_le_trans; [|apply (Z.pow_le_mono_r _ 64); solve_goal].
  done.
Qed.
