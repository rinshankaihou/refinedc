From refinedc.lang Require Import base.

Lemma binary_search_cond_1 {A} y R (l : list A) i j x z `{!Transitive R}:
  StronglySorted R l → l !! i = Some x → l !! j = Some y → (i ≤ j)%nat → R y z → R x z.
Proof.
  move => ?????.
  have [||||->|?]:= StronglySorted_lookup_le R l i j x y => //. by etrans.
Qed.

Lemma binary_search_cond_2 {A} y R (l : list A) i j x z `{!Transitive R}:
  StronglySorted R l → l !! i = Some x → l !! j = Some y → (j ≤ i)%nat → ¬ R y z → ¬ R x z.
Proof.
  move => ???? Hneg. have [||||<-|?]:= StronglySorted_lookup_le R l j i y x => //.
  contradict Hneg. by etrans.
Qed.
