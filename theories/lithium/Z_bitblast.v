From Coq Require Import ssreflect.
From stdpp Require Import prelude.
From Coq.btauto Require Export Btauto.


(** * Settings *)
(* set globally in base.v *)
Local Set Keyed Unification.

Local Open Scope bool_scope.
Local Open Scope Z_scope.

(** * Helper lemmas to upstream *)
Lemma Nat_eqb_eq n1 n2 :
  (n1 =? n2)%nat = bool_decide (n1 = n2).
Proof. case_bool_decide; [by apply Nat.eqb_eq | by apply Nat.eqb_neq]. Qed.
Lemma Z_eqb_eq n1 n2 :
  (n1 =? n2)%Z = bool_decide (n1 = n2).
Proof. case_bool_decide; [by apply Z.eqb_eq | by apply Z.eqb_neq]. Qed.
Lemma Z_testbit_pos_testbit p n:
  (0 ≤ n)%Z →
  Z.testbit (Z.pos p) n = Pos.testbit p (Z.to_N n).
Proof. by destruct n, p. Qed.

Lemma negb_forallb {A} (ls : list A) f:
   negb (forallb f ls) = existsb (negb ∘ f) ls.
Proof. elim: ls => //= ?? <-. by rewrite negb_andb. Qed.

Lemma Z_bits_inj'' a b:
  a = b → (∀ n : Z, 0 ≤ n → Z.testbit a n = Z.testbit b n).
Proof. apply Z.bits_inj_iff'. Qed.

Lemma tac_tactic_in_hyp (P1 P2 : Prop):
  P1 → (P1 → P2) → P2.
Proof. eauto. Qed.
(** TODO: replace this with [do [ tac ] in H] from ssreflect? *)
Tactic Notation "tactic" tactic3(tac) "in" ident(H) :=
  let H' := fresh in
  unshelve epose proof (tac_tactic_in_hyp _ _ H _) as H'; [shelve|
    tac; let H := fresh H in intros H; exact H |];
  clear H; rename H' into H.

(** ** bitranges *)
Fixpoint pos_to_bit_ranges_aux (p : positive) : (nat * nat) * list (nat * nat) :=
  match p with
  | xH => ((0, 1)%nat, [])
  | xO p' =>
      let x := pos_to_bit_ranges_aux p' in
      ((S x.1.1, x.1.2), prod_map S id <$> x.2)
  | xI p' =>
      let x := pos_to_bit_ranges_aux p' in
      if (x.1.1 =? 0)%nat then
        ((0%nat, S x.1.2), prod_map S id <$> x.2)
      else
        ((0%nat, 1%nat), prod_map S id <$> (x.1 :: x.2))
  end.

(* Compute (pos_to_bit_ranges_aux 1%positive). (** 0b  1  (0, 1), [] *) *)
(* Compute (pos_to_bit_ranges_aux 2%positive). (** 0b 10  (1, 1), [] *) *)
(* Compute (pos_to_bit_ranges_aux 3%positive). (** 0b 11  (0, 2), [] *) *)
(* Compute (pos_to_bit_ranges_aux 4%positive). (** 0b100  (2, 1), [] *) *)
(* Compute (pos_to_bit_ranges_aux 5%positive). (** 0b101  (0, 1), [(2, 1)] *) *)
(* Compute (pos_to_bit_ranges_aux 6%positive). (** 0b110  (1, 2), [] *) *)
(* Compute (pos_to_bit_ranges_aux 7%positive). (** 0b111  (0, 3), [] *) *)
(* Compute (pos_to_bit_ranges_aux 21%positive). (** 0b10101  (0, 1), [(2, 1), (4, 1)] *) *)

Definition pos_to_bit_ranges (p : positive) : list (nat * nat) :=
  let x := pos_to_bit_ranges_aux p in x.1::x.2.

Lemma pos_to_bit_ranges_spec p rs:
  pos_to_bit_ranges p = rs →
  (∀ n, Pos.testbit p n ↔ ∃ r, r ∈ rs ∧ (N.of_nat r.1 ≤ n ∧ n < N.of_nat r.1 + N.of_nat r.2)%N).
Proof.
  unfold pos_to_bit_ranges => <-.
  elim: p => //; csimpl.
  - move => p IH n. rewrite Nat_eqb_eq. case_match; subst.
    + split; [|done] => _. case_match.
      all: eexists _; split; [by apply elem_of_list_here|] => /=; lia.
    + rewrite {}IH. split; move => [r[/elem_of_cons[Heq|Hin] ?]]; simplify_eq/=.
      * (* r = (pos_to_bit_ranges_aux p).1 *)
        case_bool_decide as Heq; simplify_eq/=.
        -- eexists _. split; [by apply elem_of_list_here|] => /=. lia.
        -- eexists _. split. { apply elem_of_list_further. apply elem_of_list_here. }
          simplify_eq/=. lia.
      * (* r ∈ (pos_to_bit_ranges_aux p).2 *)
        case_bool_decide as Heq; simplify_eq/=.
        -- eexists _. split. { apply elem_of_list_further. apply elem_of_list_fmap. by eexists _. }
           simplify_eq/=. lia.
        -- eexists _. split. { do 2 apply elem_of_list_further. apply elem_of_list_fmap. by eexists _. }
           simplify_eq/=. lia.
      * eexists _. split; [by apply elem_of_list_here|]. case_bool_decide as Heq; simplify_eq/=; lia.
      * case_bool_decide as Heq; simplify_eq/=.
        -- move: Hin => /= /elem_of_list_fmap[?[??]]; subst. eexists _. split; [by apply elem_of_list_further |].
           simplify_eq/=. lia.
        -- rewrite -fmap_cons in Hin. move: Hin => /elem_of_list_fmap[?[??]]; subst. naive_solver lia.
  - move => p IH n. case_match; subst.
    + split; [done|] => -[[l h][/elem_of_cons[?|/(elem_of_list_fmap_2 _ _ _)[[??][??]]]?]]; simplify_eq/=; lia.
    + rewrite IH. split; move => [r[/elem_of_cons[Heq|Hin] ?]]; simplify_eq/=.
      * eexists _. split; [by apply elem_of_list_here|] => /=; lia.
      * eexists _. split. { apply elem_of_list_further. apply elem_of_list_fmap. by eexists _. }
        destruct r; simplify_eq/=. lia.
      * eexists _. split; [by apply elem_of_list_here|] => /=; lia.
      * move: Hin => /elem_of_list_fmap[r'[??]]; subst. eexists _. split; [by apply elem_of_list_further|].
         destruct r'; simplify_eq/=. lia.
  - move => n. setoid_rewrite elem_of_list_singleton. case_match; split => //; subst; naive_solver lia.
Qed.

Definition Z_to_bit_ranges (z : Z) : list (nat * nat) :=
  match z with
  | Z0 => []
  | Z.pos p => pos_to_bit_ranges p
  | Z.neg p => []
  end.

Lemma Z_to_bit_ranges_spec z n rs:
  (0 ≤ n)%Z →
  (0 ≤ z)%Z →
  Z_to_bit_ranges z = rs →
  Z.testbit z n ↔ Exists (λ r, Z.of_nat r.1 ≤ n ∧ n < Z.of_nat r.1 + Z.of_nat r.2) rs.
Proof.
  move => /= ??.
  destruct z => //=.
  + move => <-. rewrite Z.bits_0 Exists_nil. done.
  + move => /pos_to_bit_ranges_spec Hbit. rewrite Z_testbit_pos_testbit // Hbit Exists_exists. naive_solver lia.
Qed.

(** * [simplify_bool_eq] *)
Create HintDb simplify_bool_eq_db discriminated.

#[export] Hint Rewrite
  Bool.andb_false_r
  Bool.andb_true_r
  Bool.andb_false_l
  Bool.andb_true_l
  Bool.orb_false_r
  Bool.orb_true_r
  Bool.orb_false_l
  Bool.orb_true_l
  Bool.xorb_false_r
  Bool.xorb_true_r
  Bool.xorb_false_l
  Bool.xorb_true_l
  : simplify_bool_eq_db.

Ltac simplify_bool_eq :=
  cbn [andb orb];
  autorewrite with simplify_bool_eq_db.

(** * [simplify_bitblast_index] *)
Create HintDb simplify_bitblast_index_db discriminated.

#[export] Hint Rewrite
  Z.sub_add
  Z.add_simpl_r
  : simplify_bitblast_index_db.

Local Ltac simplify_bitblast_index := autorewrite with simplify_bitblast_index_db.

(** * Main typeclasses for bitblast *)
Create HintDb bitblast discriminated.
Global Hint Constants Opaque : bitblast.
Global Hint Constants Opaque : bitblast.

(** ** [IsPowerOfTwo] *)
Class IsPowerOfTwo (z n : Z) := {
  is_power_of_two_proof : z = 2 ^ n;
}.
Global Arguments is_power_of_two_proof _ _ {_}.
Global Hint Mode IsPowerOfTwo + - : bitblast.
Lemma is_power_of_two_pow2 n:
  IsPowerOfTwo (2 ^ n) n.
Proof. constructor. done. Qed.
Global Hint Resolve is_power_of_two_pow2 | 10 : bitblast.
Lemma is_power_of_two_const n p:
  (∀ x, [(n, 1%nat)] = x → prod_map Z.of_nat id <$> Z_to_bit_ranges (Z.pos p) = x) →
  IsPowerOfTwo (Z.pos p) n.
Proof.
  move => Hn. constructor. have {}Hn := Hn _ ltac:(done).
  apply Z.bits_inj_iff' => i ?.
  apply eq_bool_prop_intro. rewrite Z_to_bit_ranges_spec; [|done|lia|done].
  move: Hn => /(fmap_cons_inv _ _ _)[[n' ?][?/=[[??][/(@eq_sym _ _ _)/fmap_nil_inv->->]]]]. subst.
  rewrite Exists_cons Exists_nil /=.
  rewrite Z.pow2_bits_eqb ?Z_eqb_eq ?bool_decide_spec; lia.
Qed.
Global Hint Extern 10 (IsPowerOfTwo (Z.pos ?p) _) =>
  lazymatch isPcst p with | true => idtac end;
  simple notypeclasses refine (is_power_of_two_const _ _ _);
   let H := fresh in intros ? H; vm_compute; apply H
  : bitblast.

(** ** [BitblastBounded] *)
Class BitblastBounded (z n : Z) := {
  bitblast_bounded_proof : 0 ≤ z < 2 ^ n;
}.
Global Arguments bitblast_bounded_proof _ _ {_}.
Global Hint Mode BitblastBounded + - : bitblast.

Global Hint Extern 10 (BitblastBounded _ _) =>
  constructor; first [ split; [lia|done] | done]
  : bitblast.

(** ** [Bitblast] *)
Class Bitblast (z n : Z) (b : bool) := {
  bitblast_proof : Z.testbit z n = b;
}.
Global Arguments bitblast_proof _ _ _ {_}.
Global Hint Mode Bitblast + + - : bitblast.

Definition BITBLAST_TESTBIT := Z.testbit.
Lemma bitblast_id z n:
  Bitblast z n (bool_decide (0 ≤ n) && BITBLAST_TESTBIT z n).
Proof. constructor. case_bool_decide => //=. rewrite Z.testbit_neg_r //; lia. Qed.
Global Hint Resolve bitblast_id | 1000 : bitblast.
Lemma bitblast_id_bounded z z' n:
  BitblastBounded z z' →
  Bitblast z n (bool_decide (0 ≤ n < z') && BITBLAST_TESTBIT z n).
Proof.
  move => [Hb]. constructor.
  move: (Hb) => /Z_bounded_iff_bits_nonneg' Hn.
  case_bool_decide => //=.
  destruct (decide (0 ≤ n)); [|rewrite Z.testbit_neg_r //; lia].
  apply Hn; try lia.
  destruct (decide (0 ≤ z')) => //.
  rewrite Z.pow_neg_r in Hb; lia.
Qed.
Global Hint Resolve bitblast_id_bounded | 990 : bitblast.
Lemma bitblast_0 n:
  Bitblast 0 n false.
Proof. constructor. by rewrite Z.bits_0. Qed.
Global Hint Resolve bitblast_0 | 10 : bitblast.
Lemma bitblast_pos p n rs b:
  (∀ x, rs = x → (λ p, (Z.of_nat p.1, Z.of_nat p.1 + Z.of_nat p.2)) <$> Z_to_bit_ranges (Z.pos p) = x) →
  existsb (λ '(r1, r2), bool_decide (r1 ≤ n ∧ n < r2)) rs = b →
  Bitblast (Z.pos p) n b.
Proof.
  move => Hr <-. constructor. rewrite -(Hr rs) //.
  destruct (decide (0 ≤ n)). 2: {
    rewrite Z.testbit_neg_r; [lia|]. elim: (Z_to_bit_ranges (Z.pos p)) => // [??]; csimpl => <-.
    case_bool_decide => //; lia.
  }
  apply eq_bool_prop_intro. rewrite Z_to_bit_ranges_spec; [|done..]. rewrite existb_True Exists_fmap.
  f_equiv => -[??] /=. by rewrite bool_decide_spec.
Qed.
Global Hint Extern 10 (Bitblast (Z.pos ?p) _ _) =>
  lazymatch isPcst p with | true => idtac end;
  simple notypeclasses refine (bitblast_pos _ _ _ _ _ _);[shelve|
   let H := fresh in intros ? H; vm_compute; apply H |
   cbv [existsb]; exact eq_refl]
  : bitblast.
Lemma bitblast_neg p n rs b:
  (∀ x, rs = x → (λ p, (Z.of_nat p.1, Z.of_nat p.1 + Z.of_nat p.2)) <$> Z_to_bit_ranges (Z.pred (Z.pos p)) = x) →
  forallb (λ '(r1, r2), bool_decide (n < r1 ∨ r2 ≤ n)) rs = b →
  Bitblast (Z.neg p) n (bool_decide (0 ≤ n) && b).
Proof.
  move => Hr <-. constructor. rewrite -(Hr rs) //.
  case_bool_decide => /=; [|rewrite Z.testbit_neg_r; [lia|done]].
  have -> : Z.neg p = Z.lnot (Z.pred (Z.pos p)).
  { rewrite -Pos2Z.opp_pos. have := Z.add_lnot_diag (Z.pred (Z.pos p)). lia. }
  rewrite Z.lnot_spec //. symmetry. apply negb_sym.
  apply eq_bool_prop_intro. rewrite Z_to_bit_ranges_spec; [|done|lia|done].
  rewrite negb_forallb existb_True Exists_fmap.
  f_equiv => -[??] /=. rewrite negb_True bool_decide_spec. lia.
Qed.
Global Hint Extern 10 (Bitblast (Z.neg ?p) _ _) =>
  lazymatch isPcst p with | true => idtac end;
  simple notypeclasses refine (bitblast_neg _ _ _ _ _ _);[shelve|shelve|
   let H := fresh in intros ? H; vm_compute; apply H |
   cbv [forallb]; exact eq_refl]
    : bitblast.
Lemma bitblast_land z1 z2 n b1 b2:
  Bitblast z1 n b1 →
  Bitblast z2 n b2 →
  Bitblast (Z.land z1 z2) n (b1 && b2).
Proof. move => [<-] [<-]. constructor. by rewrite Z.land_spec. Qed.
Global Hint Resolve bitblast_land | 10 : bitblast.
Lemma bitblast_lor z1 z2 n b1 b2:
  Bitblast z1 n b1 →
  Bitblast z2 n b2 →
  Bitblast (Z.lor z1 z2) n (b1 || b2).
Proof. move => [<-] [<-]. constructor. by rewrite Z.lor_spec. Qed.
Global Hint Resolve bitblast_lor | 10 : bitblast.
Lemma bitblast_lxor z1 z2 n b1 b2:
  Bitblast z1 n b1 →
  Bitblast z2 n b2 →
  Bitblast (Z.lxor z1 z2) n (xorb b1 b2).
Proof. move => [<-] [<-]. constructor. by rewrite Z.lxor_spec. Qed.
Global Hint Resolve bitblast_lxor | 10 : bitblast.
Lemma bitblast_shiftr z1 z2 n b1:
  Bitblast z1 (n + z2) b1 →
  Bitblast (z1 ≫ z2) n (bool_decide (0 ≤ n) && b1).
Proof.
  move => [<-]. constructor.
  case_bool_decide => /=; [by rewrite Z.shiftr_spec| rewrite Z.testbit_neg_r //; lia].
Qed.
Global Hint Resolve bitblast_shiftr | 10 : bitblast.
Lemma bitblast_shiftl z1 z2 n b1:
  Bitblast z1 (n - z2) b1 →
  Bitblast (z1 ≪ z2) n (bool_decide (0 ≤ n) && b1).
Proof.
  move => [<-]. constructor.
  case_bool_decide => /=; [by rewrite Z.shiftl_spec| rewrite Z.testbit_neg_r //; lia].
Qed.
Global Hint Resolve bitblast_shiftl | 10 : bitblast.
Lemma bitblast_lnot z1 n b1:
  Bitblast z1 n b1 →
  Bitblast (Z.lnot z1) n (bool_decide (0 ≤ n) && negb b1).
Proof.
  move => [<-]. constructor.
  case_bool_decide => /=; [by rewrite Z.lnot_spec| rewrite Z.testbit_neg_r //; lia].
Qed.
Global Hint Resolve bitblast_lnot | 10 : bitblast.
Lemma bitblast_ldiff z1 z2 n b1 b2:
  Bitblast z1 n b1 →
  Bitblast z2 n b2 →
  Bitblast (Z.ldiff z1 z2) n (b1 && negb b2).
Proof. move => [<-] [<-]. constructor. by rewrite Z.ldiff_spec. Qed.
Global Hint Resolve bitblast_ldiff | 10 : bitblast.
Lemma bitblast_ones z1 n:
  Bitblast (Z.ones z1) n (bool_decide (0 ≤ n < z1) || bool_decide (z1 < 0 ∧ 0 ≤ n)).
Proof.
  constructor. case_bool_decide; [by apply Z.ones_spec_low|] => /=.
  case_bool_decide.
  - rewrite Z.ones_equiv Z.pow_neg_r; [lia|]. apply Z.bits_m1. lia.
  - destruct (decide (0 ≤ n)); [|rewrite Z.testbit_neg_r //; lia].
    apply Z.ones_spec_high; lia.
Qed.
Global Hint Resolve bitblast_ones | 10 : bitblast.
Lemma bitblast_pow2 n n':
  Bitblast (2 ^ n') n (bool_decide (n = n' ∧ 0 ≤ n)).
Proof.
  constructor. case_bool_decide; destruct_and?; subst; [by apply Z.pow2_bits_true|].
  destruct (decide (0 ≤ n)); [|rewrite Z.testbit_neg_r //; lia].
  apply Z.pow2_bits_false. lia.
Qed.
Global Hint Resolve bitblast_pow2 | 10 : bitblast.
Lemma bitblast_setbit z1 n b1 n':
  Bitblast (Z.lor z1 (2 ^ n')) n b1 →
  Bitblast (Z.setbit z1 n') n b1.
Proof. by rewrite Z.setbit_spec'. Qed.
Global Hint Resolve bitblast_setbit | 10 : bitblast.
Lemma bitblast_mod z1 z2 z2' n b1:
  IsPowerOfTwo z2 z2' →
  Bitblast z1 n b1 →
  Bitblast (z1 `mod` z2) n (bool_decide (0 ≤ n) && ((bool_decide (z2' < 0) || bool_decide (n < z2')) && b1)).
Proof.
  move => [->] [<-]. constructor.
  case_bool_decide => /=; [|rewrite Z.testbit_neg_r //;lia].
  case_bool_decide => /=. { by rewrite Z.pow_neg_r ?Zmod_0_r; [lia|]. }
  rewrite -Z.land_ones; [lia|]. rewrite Z.land_spec Z_ones_spec; [lia..|].
  by rewrite andb_comm.
Qed.
Global Hint Resolve bitblast_mod | 10 : bitblast.
(* TODO: What are good instances for +? Maybe something based on Z_add_nocarry_lor? *)
Lemma bitblast_add_0 z1 z2 b1 b2:
  Bitblast z1 0 b1 →
  Bitblast z2 0 b2 →
  Bitblast (z1 + z2) 0 (xorb b1 b2).
Proof. move => [<-] [<-]. constructor. apply Z.add_bit0. Qed.
Global Hint Resolve bitblast_add_0 | 5 : bitblast.
Lemma bitblast_add_1 z1 z2 b10 b11 b20 b21:
  Bitblast z1 0 b10 →
  Bitblast z2 0 b20 →
  Bitblast z1 1 b11 →
  Bitblast z2 1 b21 →
  Bitblast (z1 + z2) 1 (xorb (xorb b11 b21) (b10 && b20)).
Proof. move => [<-] [<-] [<-] [<-]. constructor. apply Z.add_bit1. Qed.
Global Hint Resolve bitblast_add_1 | 5 : bitblast.

(** * Tactics *)

(** ** Helper definitions and lemmas for the tactics *)
Definition BITBLAST_BOOL_DECIDE := @bool_decide.
Arguments BITBLAST_BOOL_DECIDE _ {_}.

Lemma tac_bitblast_bool_decide_true G (P : Prop) `{!Decision P}:
  P →
  G true →
  G (bool_decide P).
Proof. move => ??. by rewrite bool_decide_eq_true_2. Qed.
Lemma tac_bitblast_bool_decide_false G (P : Prop) `{!Decision P}:
  ¬ P →
  G false →
  G (bool_decide P).
Proof. move => ??. by rewrite bool_decide_eq_false_2. Qed.
Lemma tac_bitblast_bool_decide_split G (P : Prop) `{!Decision P}:
  (P → G true) →
  (¬ P → G false) →
  G (bool_decide P).
Proof. move => ??. case_bool_decide; eauto. Qed.

(** ** Core tactics *)
Ltac bitblast_done :=
  solve [ first [ done | lia | btauto ] ].

(** [bitblast_blast_eq] applies to goals of the form [Z.testbit _ _ = ?x] and bitblasts the
  Z.testbit using the [Bitblast] typeclass. *)
Ltac bitblast_blast_eq :=
  lazymatch goal with |- Z.testbit _ _ = _ => idtac end;
  etrans; [ notypeclasses refine (bitblast_proof _ _ _); typeclasses eauto with bitblast | ];
  simplify_bitblast_index;
  exact eq_refl.

(** [bitblast_bool_decide_simplify] get rids of unnecessary bool_decide in the goal. *)
Ltac bitblast_bool_decide_simplify :=
  repeat lazymatch goal with
         | |- context [@bool_decide ?P ?Dec] =>
             pattern (@bool_decide P Dec);
             lazymatch goal with
             | |- ?G _ =>
                 first [
                     refine (@tac_bitblast_bool_decide_true G P Dec _ _); [lia|];
                     cbv beta; simplify_bool_eq
                   |
                     refine (@tac_bitblast_bool_decide_false G P Dec _ _); [lia|];
                     cbv beta; simplify_bool_eq
                   |
                     change_no_check (G (@BITBLAST_BOOL_DECIDE P Dec))
               ]
             end;
             cbv beta
         end;
  lazymatch goal with
  | |- ?G => let x := eval unfold BITBLAST_BOOL_DECIDE in G in change_no_check x
  end.

(** [bitblast_bool_decide_split] performs a case distinction on a bool_decide in the goal. *)
Ltac bitblast_bool_decide_split :=
  lazymatch goal with
  | |- context [@bool_decide ?P ?Dec] =>
      pattern (@bool_decide P Dec);
      lazymatch goal with
      | |- ?G _ =>
          refine (@tac_bitblast_bool_decide_split G P Dec _ _) => ?; cbv beta; simplify_bool_eq
      end
  end.

(** [bitblast_unfold] bitblasts all [Z.testbit] in the goal. *)
Ltac bitblast_unfold :=
  repeat lazymatch goal with
  | |- context [Z.testbit ?z ?n] =>
      pattern (Z.testbit z n);
      simple refine (eq_rec_r _ _ _); [shelve| |bitblast_blast_eq]; cbn beta
  end;
  lazymatch goal with
  | |- ?G => let x := eval unfold BITBLAST_TESTBIT in G in change_no_check x
  end.

(** [bitblast_raw] bitblasts all [Z.testbit] in the goal and simplifies the result. *)
Ltac bitblast_raw :=
  bitblast_unfold;
  bitblast_bool_decide_simplify;
  try bitblast_done;
  repeat (bitblast_bool_decide_split; bitblast_bool_decide_simplify; try bitblast_done).

(** ** Tactic notations *)
Tactic Notation "bitblast" "as" ident(i) :=
  apply Z.bits_inj_iff'; intros i => ?; bitblast_raw.

Tactic Notation "bitblast" :=
  lazymatch goal with
  | |- context [Z.testbit _ _] => idtac
  | _ => apply Z.bits_inj_iff' => ??
  end;
  bitblast_raw.

Tactic Notation "bitblast" ident(H) :=
  tactic bitblast_unfold in H;
  tactic bitblast_bool_decide_simplify in H.
Tactic Notation "bitblast" ident(H) "with" constr(i) "as" ident(H') :=
  lazymatch type of H with
  | @eq Z _ _ => efeed pose proof (Z_bits_inj'' _ _ H i) as H'; [try bitblast_done..|]
  | ∀ x, _ => efeed pose proof (H i) as H'; [try bitblast_done..|]
  end; bitblast H'.
Tactic Notation "bitblast" ident(H) "with" constr(i) :=
  let H' := fresh "H" in bitblast H with i as H'.

(** * Tests *)

Goal ∀ x a k,
  Z.land x (Z.land (Z.ones k) (Z.ones k) ≪ a) =
  Z.land (Z.land (x ≫ a) (Z.ones k)) (Z.ones k) ≪ a.
Proof. intros. bitblast. all: fail. Abort.

Goal ∀ i,
    1 ≪ i = Z.land (Z.ones 1) (Z.ones 1) ≪ i.
Proof. intros. bitblast. all: fail. Abort.

Goal ∀ N k,
  0 ≤ k ≤ N → Z.ones N ≫ (N - k) = Z.ones k.
Proof. intros. bitblast. all: fail. Abort.

Goal ∀ z,
  Z.land z (-1) = z.
Proof. intros. bitblast. all: fail. Abort.

Goal ∀ z,
  Z.land z 0x20000 = 0 →
  Z.land (z ≫ 17) (Z.ones 1) = 0.
Proof.
  intros ? Hz. bitblast as n.
  by bitblast Hz with (n + 17).
  all: fail.
Abort.


Goal ∀ z, 0 ≤ z < 2 ^ 64 →
   Z.land z 0xfff0000000000007 = 0 ↔ z < 2 ^ 52 ∧ z `mod` 8 = 0.
Proof.
  move => z ?. split.
  - move => Hx. split.
    + apply Z_bounded_iff_bits_nonneg; [lia..|] => n ?. bitblast.
      by bitblast Hx with n.
    + bitblast as n. by bitblast Hx with n.
  - move => [H1 H2]. bitblast as n. by bitblast H2 with n.
  all: fail.
Abort.
