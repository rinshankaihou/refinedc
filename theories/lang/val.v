From refinedc.lang Require Export base byte layout int_type loc.
Set Default Proof Using "Type".
Open Scope Z_scope.

(** * Bytes and values stored in memory *)

(** Representation of a byte stored in memory. *)
Inductive mbyte : Set :=
| MByte (b : byte)
| MPtrFrag (l : loc) (n : nat) (** Fragment [n] for location [l]. *)
| MPoison.

Instance mbyte_dec_eq : EqDecision mbyte.
Proof.
  move => [b1|l1 n1|] [b2|l2 n2|]; try by right.
  - destruct (decide (b1 = b2)); [left|right]; naive_solver.
  - destruct (decide (l1 = l2 ∧ n1 = n2)); [left|right]; naive_solver.
  - by left.
Qed.

(** Representation of a value (list of bytes). *)
Definition val : Set := list mbyte.
Bind Scope val_scope with val.

(** Predicate stating that value [v] has the right size according to layout [ly]. *)
Definition has_layout_val (v : val) (ly : layout) : Prop := length v = ly.(ly_size).
Notation "v `has_layout_val` n" := (has_layout_val v n) (at level 50) : stdpp_scope.
Arguments has_layout_val : simpl never.
Typeclasses Opaque has_layout_val.

(** ** Conversion to and from locations. *)

Definition val_of_loc (l : loc) : val :=
  MPtrFrag l <$> seq 0 bytes_per_addr.

Definition val_to_loc (v : val) : option loc :=
  if v is MPtrFrag l 0 :: _ then
    if (bool_decide (v = val_of_loc l)) then Some l else None
  else None.

Lemma val_to_of_loc l: val_to_loc (val_of_loc l) = Some l.
Proof.
  by rewrite /= bool_decide_true.
Qed.

Lemma val_of_to_loc v l :
  val_to_loc v = Some l → v = val_of_loc l.
Proof.
  destruct v => //=; case_match => //; case_match => //.
  case_bool_decide; naive_solver.
Qed.

Lemma val_to_loc_length v:
  is_Some (val_to_loc v) → length v = bytes_per_addr.
Proof.
  rewrite /val_to_loc. move => [? H]. repeat case_match => //; simplify_eq.
  revert select (bool_decide _ = _) => /bool_decide_eq_true ->.
  by rewrite /val_of_loc fmap_length seq_length.
Qed.

Typeclasses Opaque val_of_loc val_to_loc.
Arguments val_of_loc : simpl never.
Arguments val_to_loc : simpl never.

(** ** Conversion to and from mathematical integers. *)

(* TODO: we currently assume little-endian, make this more generic. *)

Fixpoint val_to_Z_go v : option Z :=
  match v with
  | []           => Some 0
  | MByte b :: v => z ← val_to_Z_go v; Some (byte_modulus * z + b.(byte_val))
  | _            => None
  end.

Definition val_to_Z (v : val) (it : int_type) : option Z :=
  if decide (length v = bytes_per_int it) then
    z ← val_to_Z_go v;
    if it.(it_signed) && bool_decide (int_half_modulus it ≤ z) then
      Some (z - int_modulus it)
    else
      Some z
  else None.

Program Fixpoint val_of_Z_go (n : Z) (sz : nat) : val :=
  match sz return _ with
  | O    => []
  | S sz => MByte {| byte_val := (n `mod` byte_modulus) |}
            :: val_of_Z_go (n / byte_modulus) sz
  end.
Next Obligation. move => n. have [] := Z_mod_lt n byte_modulus => //*. lia. Qed.

Definition val_of_Z (z : Z) (it : int_type) : option val :=
  if bool_decide (z ∈ it) then
    let p := if bool_decide (z < 0) then z + int_modulus it else z in
    Some (val_of_Z_go p (bytes_per_int it))
  else
    None.

Definition i2v (n : Z) (it : int_type) : val :=
  default [MPoison] (val_of_Z n it).

Definition val_of_bool (b : bool) : val :=
  i2v (Z_of_bool b) bool_it.

Lemma val_of_Z_go_length z sz :
  length (val_of_Z_go z sz) = sz.
Proof. elim: sz z => //= ? IH ?. by f_equal. Qed.

Lemma val_to_of_int_go z (sz : nat) :
  0 ≤ z < 2 ^ (sz * bits_per_byte) →
  val_to_Z_go (val_of_Z_go z sz) = Some z.
Proof.
  rewrite /bits_per_byte.
  elim: sz z => /=. 1: rewrite /Z.of_nat; move => ??; f_equal; lia.
  move => sz IH z [? Hlt]. rewrite IH /byte_modulus /= -?Z_div_mod_eq //.
  split. apply Z_div_pos => //. apply Zdiv_lt_upper_bound => //.
  rewrite Nat2Z.inj_succ -Zmult_succ_l_reverse Z.pow_add_r // in Hlt.
  lia.
Qed.

Lemma val_of_Z_length z it v:
  val_of_Z z it = Some v → length v = bytes_per_int it.
Proof.
  rewrite /val_of_Z => Hv. case_bool_decide => //. simplify_eq.
  by rewrite val_of_Z_go_length.
Qed.

Lemma val_to_Z_length v it z:
  val_to_Z v it = Some z → length v = bytes_per_int it.
Proof. rewrite /val_to_Z. by case_decide. Qed.

Lemma val_of_Z_is_some it z:
  z ∈ it → is_Some (val_of_Z z it).
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_of_Z_in_range it z v:
  val_of_Z z it = Some v → z ∈ it.
Proof. rewrite /val_of_Z. case_bool_decide; by eauto. Qed.

Lemma val_to_Z_go_in_range v n:
  val_to_Z_go v = Some n → 0 ≤ n < 2 ^ (length v * bits_per_byte).
Proof.
  elim: v n => /=.
  - move => n [] <-. split; first lia.
    apply Z.pow_pos_nonneg; lia.
  - move => ? v IH n. case_match => //.
    destruct (val_to_Z_go v) => /=; last done.
    move => [] <-. move: (IH z eq_refl).
    move: (byte_constr b). rewrite /byte_modulus /bits_per_byte.
    move => [??] [??]. split; first lia.
    have ->: S (length v) * 8 = 8 + length v * 8 by lia.
    rewrite Z.pow_add_r; lia.
Qed.

Lemma val_to_Z_in_range v it n:
  val_to_Z v it = Some n → n ∈ it.
Proof.
  rewrite /val_to_Z. case_decide as Hlen; last done.
  destruct (val_to_Z_go v) eqn:Heq => /=; last done.
  move: Heq => /val_to_Z_go_in_range.
  rewrite Hlen /elem_of /int_elem_of_it /max_int /min_int.
  rewrite /int_half_modulus /int_modulus /bits_per_int.
  destruct (it_signed it) eqn:Hsigned => /=.
  - case_decide => /=.
    + move => [??] [] ?. simplify_eq.
      assert (2 ^ (bytes_per_int it * bits_per_byte) =
              2 * 2 ^ (bytes_per_int it * bits_per_byte - 1)) as Heq.
      { rewrite Z.sub_1_r. rewrite Z_pow_pred_r => //. rewrite /bits_per_byte.
        have ? := bytes_per_int_gt_0 it. lia. }
      rewrite Heq. lia.
    + move => [??] [] ?. lia.
  - move => [??] [] ?. lia.
Qed.

Lemma val_to_of_int z it v:
  val_of_Z z it = Some v → val_to_Z v it = Some z.
Proof.
  rewrite /val_of_Z /val_to_Z => Ht.
  destruct (bool_decide (z ∈ it)) eqn: Hr => //. simplify_eq.
  move: Hr => /bool_decide_eq_true[Hm HM].
  have Hlen := bytes_per_int_gt_0 it.
  rewrite /max_int in HM. rewrite /min_int in Hm.
  rewrite val_of_Z_go_length val_to_of_int_go /=.
  - case_decide as H => //. clear H.
    destruct (it_signed it) eqn:Hs => /=.
    + case_decide => /=; last (rewrite bool_decide_false //; lia).
      rewrite bool_decide_true; [f_equal; lia|].
      rewrite int_modulus_twice_half_modulus. move: Hm HM.
      generalize (int_half_modulus it). move => n Hm HM. lia.
    + rewrite bool_decide_false //. lia.
  - case_bool_decide as Hneg; case_match; split; try lia.
    + rewrite int_modulus_twice_half_modulus. lia.
    + rewrite /int_modulus /bits_per_int. lia.
    + rewrite /int_half_modulus in HM.
      transitivity (2 ^ (bits_per_int it -1)); first lia.
      rewrite /bits_per_int /bytes_per_int /bits_per_byte /=.
      apply Z.pow_lt_mono_r; try lia.
    + rewrite /int_modulus /bits_per_int in HM. lia.
Qed.

Lemma val_of_Z_bool b it:
  val_of_Z (Z_of_bool b) it = Some (i2v (Z_of_bool b) it).
Proof.
  have [|? Hv] := val_of_Z_is_some it (Z_of_bool b); last by rewrite /i2v Hv.
  rewrite /elem_of /int_elem_of_it.
  have ? := min_int_le_0 it. have ? := max_int_ge_127 it.
  split; destruct b => /=; lia.
Qed.

Lemma val_to_Z_bool b :
  val_to_Z (val_of_bool b) bool_it = Some (Z_of_bool b).
Proof. by destruct b. Qed.

Lemma i2v_bool_length b it:
  length (i2v (Z_of_bool b) it) = bytes_per_int it.
Proof. by have /val_of_Z_length -> := val_of_Z_bool b it. Qed.

Lemma i2v_bool_Some b it:
  val_to_Z (i2v (Z_of_bool b) it) it = Some (Z_of_bool b).
Proof. apply val_to_of_int. apply val_of_Z_bool. Qed.

Lemma val_to_Z_go_Some_inj v1 v2 n:
  length v1 = length v2 →
  val_to_Z_go v1 = Some n →
  val_to_Z_go v2 = Some n →
  v1 = v2.
Proof.
  elim: v1 v2 n; first by destruct v2.
  move => b1 v1 IH [] b2 v2 // n /= [] Hlen.
  destruct b1 as [b1|?|] => //. destruct b2 as [b2|?|] => //.
  destruct (val_to_Z_go v1) as [n1|] eqn:Hn1 => //.
  destruct (val_to_Z_go v2) as [n2|] eqn:Hn2 => //.
  move => /= [] <- [] Heq.
  assert (n1 = n2 ∧ byte_val b1 = byte_val b2) as [??].
  { move: Heq. clear.
    have H1 := byte_constr b1.
    have H2 := byte_constr b2.
    move: H1 H2. rewrite /byte_modulus. lia. }
  simplify_eq. f_equal; last by eapply IH. f_equal.
  by apply byte_eq.
Qed.

Lemma val_to_Z_Some_inj v1 v2 it n:
  val_to_Z v1 it = Some n →
  val_to_Z v2 it = Some n →
  v1 = v2.
Proof.
  rewrite /val_to_Z.
  case_decide as Hlen1; last done.
  case_decide as Hlen2; last done.
  destruct (val_to_Z_go v1) as [n1|] eqn:Hn1 => //=.
  destruct (val_to_Z_go v2) as [n2|] eqn:Hn2 => //=.
  move: (Hn1) => /val_to_Z_go_in_range [Hb1 HB1]; rewrite Hlen1 in HB1.
  move: (Hn2) => /val_to_Z_go_in_range [Hb2 HB2]; rewrite Hlen2 in HB2.
  have Hlen: length v1 = length v2 by rewrite Hlen1 Hlen2.
  move => <- Heq_if. eapply val_to_Z_go_Some_inj => //.
  rewrite Hn2; f_equal. move: Heq_if.
  rewrite /int_modulus /int_half_modulus /bits_per_int.
  destruct (it_signed it) => /=; last naive_solver.
  repeat case_bool_decide => /=; naive_solver lia.
Qed.

Arguments val_to_Z : simpl never.
Arguments val_of_Z : simpl never.
Typeclasses Opaque val_to_Z val_of_Z val_of_bool.
