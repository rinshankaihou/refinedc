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

Fixpoint val_to_int_go v : option Z :=
  match v with
  | []           => Some 0
  | MByte b :: v => z ← val_to_int_go v; Some (byte_modulus * z + b.(byte_val))
  | _            => None
  end.

Definition val_to_int (v : val) (it : int_type) : option Z :=
  if decide (length v = bytes_per_int it) then
    z ← val_to_int_go v;
    if it.(it_signed) && bool_decide (int_half_modulus it ≤ z) then
      Some (z - int_modulus it)
    else
      Some z
  else None.

Program Fixpoint val_of_int_go (n : Z) (sz : nat) : val :=
  match sz return _ with
  | O    => []
  | S sz => MByte {| byte_val := (n `mod` byte_modulus) |}
            :: val_of_int_go (n / byte_modulus) sz
  end.
Next Obligation. move => n. have [] := Z_mod_lt n byte_modulus => //*. lia. Qed.

Definition val_of_int (z : Z) (it : int_type) : option val :=
  if bool_decide (z ∈ it) then
    let p := if bool_decide (z < 0) then z + int_modulus it else z in
    Some (val_of_int_go p (bytes_per_int it))
  else
    None.

Definition i2v (n : Z) (it : int_type) : val :=
  default [MPoison] (val_of_int n it).

Definition val_of_bool (b : bool) : val :=
  i2v (Z_of_bool b) bool_it.

Lemma val_of_int_go_length z sz :
  length (val_of_int_go z sz) = sz.
Proof. elim: sz z => //= ? IH ?. by f_equal. Qed.

Lemma val_to_of_int_go z (sz : nat) :
  0 ≤ z < 2 ^ (sz * bits_per_byte) →
  val_to_int_go (val_of_int_go z sz) = Some z.
Proof.
  rewrite /bits_per_byte.
  elim: sz z => /=. 1: rewrite /Z.of_nat; move => ??; f_equal; lia.
  move => sz IH z [? Hlt]. rewrite IH /byte_modulus /= -?Z_div_mod_eq //.
  split. apply Z_div_pos => //. apply Zdiv_lt_upper_bound => //.
  rewrite Nat2Z.inj_succ -Zmult_succ_l_reverse Z.pow_add_r // in Hlt.
  lia.
Qed.

Lemma val_of_int_length z it v:
  val_of_int z it = Some v → length v = bytes_per_int it.
Proof.
  rewrite /val_of_int => Hv. case_bool_decide => //. simplify_eq.
  by rewrite val_of_int_go_length.
Qed.

Lemma val_to_int_length v it z:
  val_to_int v it = Some z → length v = bytes_per_int it.
Proof. rewrite /val_to_int. by case_decide. Qed.

Lemma val_of_int_is_some it z:
  z ∈ it → is_Some (val_of_int z it).
Proof. rewrite /val_of_int. case_bool_decide; by eauto. Qed.

Lemma val_of_int_in_range it z v:
  val_of_int z it = Some v → z ∈ it.
Proof. rewrite /val_of_int. case_bool_decide; by eauto. Qed.

Lemma val_to_of_int z it v:
  val_of_int z it = Some v → val_to_int v it = Some z.
Proof.
  rewrite /val_of_int /val_to_int => Ht.
  destruct (bool_decide (z ∈ it)) eqn: Hr => //. simplify_eq.
  move: Hr => /bool_decide_eq_true[Hm HM].
  have Hlen := bytes_per_int_gt_0 it.
  rewrite /max_int in HM. rewrite /min_int in Hm.
  rewrite val_of_int_go_length val_to_of_int_go /=.
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

Lemma val_of_int_bool b it:
  val_of_int (Z_of_bool b) it = Some (i2v (Z_of_bool b) it).
Proof.
  have [|? Hv] := val_of_int_is_some it (Z_of_bool b); last by rewrite /i2v Hv.
  rewrite /elem_of /int_elem_of_it.
  have ? := min_int_le_0 it. have ? := max_int_ge_127 it.
  split; destruct b => /=; lia.
Qed.

Lemma val_to_int_bool b :
  val_to_int (val_of_bool b) bool_it = Some (Z_of_bool b).
Proof. by destruct b. Qed.

Lemma i2v_bool_length b it:
  length (i2v (Z_of_bool b) it) = bytes_per_int it.
Proof. by have /val_of_int_length -> := val_of_int_bool b it. Qed.

Lemma i2v_bool_Some b it:
  val_to_int (i2v (Z_of_bool b) it) it = Some (Z_of_bool b).
Proof. apply val_to_of_int. apply val_of_int_bool. Qed.

Arguments val_to_int : simpl never.
Arguments val_of_int : simpl never.
Typeclasses Opaque val_to_int val_of_int val_of_bool.
