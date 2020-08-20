From Coq Require Export ssreflect.
From Coq.ZArith Require Import Znumtheory.
From stdpp Require Import gmap list.
From stdpp Require Export sorting.
From iris.program_logic Require Import weakestpre.
From iris.bi Require Import derived_laws.
From iris.algebra Require Export big_op.
Import interface.bi derived_laws.bi.
From iris.proofmode Require Import tactics.
From stdpp Require Import natmap.
Set Default Proof Using "Type".

Global Unset Program Cases.
Global Set Keyed Unification.
Typeclasses Opaque Z.divide Z.modulo Z.div.
Arguments min : simpl nomatch.

Notation "'[@{' A '}' x ; y ; .. ; z ]" :=  (@cons A x (@cons A y .. (@cons A z (@nil A)) ..)) (only parsing) : list_scope.
Notation "'[@{' A '}' x ]" := (@cons A x nil) (only parsing) : list_scope.
Notation "'[@{' A '}' ]" := (@nil A) (only parsing) : list_scope.

Lemma rel_to_eq {A} (R : A → A → Prop) `{!Reflexive R} x y:
  x = y → R x y.
Proof. move => ->. reflexivity. Qed.

Ltac fast_reflexivity :=
  notypeclasses refine (rel_to_eq _ _ _ _); [solve [refine _] |];
  lazymatch goal with
  | |- ?x = ?y => lazymatch x with | y => exact: (eq_refl x) end
  end.


Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.
Typeclasses Opaque Z_of_bool.

Lemma big_sepL2_fupd `{BiFUpd PROP} {A B} E (Φ : nat → A → B → PROP) l1 l2 :
  ([∗ list] k↦x;y ∈ l1;l2, |={E}=> Φ k x y) ={E}=∗ [∗ list] k↦x;y ∈ l1;l2, Φ k x y.
Proof. rewrite !big_sepL2_alt. iIntros "[$ H]". by iApply big_sepL_fupd. Qed.
Lemma big_sepL2_replicate_2 {A B} {PROP : bi} (l : list A) (x : B) (Φ : nat → A → B → PROP):
  (([∗ list] k↦x1 ∈ l, Φ k x1 x) ⊣⊢ [∗ list] k↦x1;x2 ∈ l;replicate (length l) x, Φ k x1 x2).
Proof. elim: l Φ => //= ?? IH Φ. f_equiv. apply: IH. Qed.


(* TODO: does something like this exist in Iris? *)
Definition apply_dfun {A B} (f : A -d> B) (x : A) : B := f x.
Arguments apply_dfun : simpl never.

Global Instance apply_dfun_ne A B n:
  Proper ((dist n) ==> (=) ==> (dist n)) (@apply_dfun A B).
Proof. intros ?? H1 ?? ->. rewrite /apply_dfun. apply H1. Qed.

Global Instance apply_dfun_proper A B :
  Proper ((≡) ==> (=) ==> (≡)) (@apply_dfun A B).
Proof. intros ?? H1 ?? ->. rewrite /apply_dfun. apply H1. Qed.

Global Instance discrete_fn_proper A B `{LeibnizEquiv A} (f : A -d> B):
  Proper ((≡) ==> (≡)) f.
Proof. by intros ?? ->%leibniz_equiv. Qed.

(* upstream ? *)
Lemma zip_fmap_r {A B C} (l1 : list A) (l2 : list B) (f : B → C) :
  zip l1 (f <$> l2) = (λ x, (x.1, f x.2)) <$>  zip l1 l2.
Proof. rewrite zip_with_fmap_r zip_with_zip. by apply: list_fmap_ext => // [[]]. Qed.
Lemma entails_eq {PROP : bi} (P1 P2 : PROP) :
  P1 = P2 → P1 -∗ P2.
Proof. move => ->. reflexivity. Qed.


Inductive TCOneIsSome {A} : option A → option A → Prop :=
| tc_one_is_some_left n1 o2 : TCOneIsSome (Some n1) o2
| tc_one_is_some_right o1 n2 : TCOneIsSome o1 (Some n2).
Existing Class TCOneIsSome.
Global Existing Instance tc_one_is_some_left.
Global Existing Instance tc_one_is_some_right.

Inductive TCOneIsSome3 {A} : option A → option A → option A → Prop :=
| tc_one_is_some3_left n1 o2 o3 : TCOneIsSome3 (Some n1) o2 o3
| tc_one_is_some3_middle o1 n2 o3 : TCOneIsSome3 o1 (Some n2) o3
| tc_one_is_some3_right o1 o2 n3 : TCOneIsSome3 o1 o2 (Some n3).
Existing Class TCOneIsSome3.
Global Existing Instance tc_one_is_some3_left.
Global Existing Instance tc_one_is_some3_middle.
Global Existing Instance tc_one_is_some3_right.

Lemma take_elem_of {A} (x : A) n l:
  x ∈ take n l ↔ ∃ i, (i < n)%nat ∧ l !! i = Some x.
Proof.
  rewrite elem_of_list_lookup. f_equiv => i.
  destruct (decide (i < n)%nat);[rewrite lookup_take | rewrite lookup_take_ge]; naive_solver lia.
Qed.

Lemma list_find_Some' A (l : list A) x P `{!∀ x, Decision (P x)}:
  list_find P l = Some x ↔ l !! x.1 = Some x.2 ∧ P x.2 ∧ ∀ y, y ∈ take x.1 l → ¬P y.
Proof.
  destruct x => /=. rewrite list_find_Some. do 2 f_equiv. setoid_rewrite take_elem_of.
  split => ?; [naive_solver..|].
  move => j ? ?. have [|??]:= lookup_lt_is_Some_2 l j. { by apply: lookup_lt_Some. }
  set_solver.
Qed.


Section theorems.
Context `{FinMap K M}.

Lemma partial_alter_self_alt' {A} (m : M A) i f:
  m !! i = f (m !! i) → partial_alter f i m = m.
Proof using Type*.
  intros. apply map_eq. intros ii. by destruct (decide (i = ii)) as [->|];
    rewrite ?lookup_partial_alter ?lookup_partial_alter_ne.
Qed.

Lemma partial_alter_to_insert {A} x (m : M A) f k:
    f (m !! k) = Some x →
    partial_alter f k m = <[k := x]> m.
Proof using Type*. move => ?. by apply: partial_alter_ext => ? <-. Qed.

End theorems.

Global Instance set_unfold_replicate A (x y : A) n:
  SetUnfoldElemOf x (replicate n y) (x = y ∧ n ≠ 0%nat).
Proof. constructor. apply elem_of_replicate. Qed.

Lemma list_elem_of_insert1 {A} (l : list A) i (x1 x2 : A) :
  x1 ∈ <[i:=x2]> l → x1 = x2 ∨ x1 ∈ l.
Proof.
  destruct (decide (i < length l)%nat). 2: rewrite list_insert_ge; naive_solver lia.
  move => /(elem_of_list_lookup_1 _ _)[i' ].
  destruct (decide (i = i')); subst.
  - rewrite list_lookup_insert // => -[]. naive_solver.
  - rewrite list_lookup_insert_ne // elem_of_list_lookup. naive_solver.
Qed.

Lemma list_elem_of_insert2 {A} (l : list A) i (x1 x2 x3 : A) :
  l !! i = Some x3 → x1 ∈ l → x1 ∈ <[i:=x2]> l ∨ x1 = x3.
Proof.
  destruct (decide (i < length l)%nat). 2: rewrite list_insert_ge; naive_solver lia.
  move => ? /(elem_of_list_lookup_1 _ _)[i' ?].
  destruct (decide (i = i')); simplify_eq; first naive_solver.
  left. apply elem_of_list_lookup. exists i'. by rewrite list_lookup_insert_ne.
Qed.
Lemma list_elem_of_insert2' {A} (l : list A) i (x1 x2 x3 : A) :
  l !! i = Some x3 → x1 ∈ l → x1 ≠ x3 → x1 ∈ <[i:=x2]> l.
Proof. move => ???. efeed pose proof (list_elem_of_insert2 (A:=A)) as Hi; naive_solver. Qed.

Lemma apply_default {A B} (f : A → B) (d : A) (o : option A) :
  f (default d o) = default (f d) (f <$> o).
Proof. by destruct o. Qed.

Lemma list_fmap_ext' {A B} f (g : A → B) (l1 l2 : list A) :
    (∀ x, x ∈ l1 → f x = g x) → l1 = l2 → f <$> l1 = g <$> l2.
Proof. intros ? <-. induction l1; f_equal/=; set_solver. Qed.


Lemma imap_fst_NoDup {A B C} l (f : nat → A → B) (g : nat → C):
  Inj eq eq g →
  NoDup (imap (λ i o, (g i, f i o)) l).*1.
Proof.
  move => ?. rewrite fmap_imap (imap_ext _ (λ i o, g i)%nat) // imap_seq_0.
    by apply NoDup_fmap, NoDup_ListNoDup, seq_NoDup.
Qed.
Global Instance set_unfold_imap A B f (l : list A) (x : B):
  SetUnfoldElemOf x (imap f l) (∃ i y, x = f i y ∧ l !! i = Some y).
Proof.
  constructor.
  elim: l f => /=. set_solver. set_unfold. move => ? ? IH f.
  rewrite IH {IH}. split. case.
  - move => ->. set_solver.
  - move => [n [v [-> ?]]]. exists (S n), v => /=. set_solver.
  - move => [[|n] /= [v [-> ?]]]; simplify_eq; [by left | right].
    naive_solver.
Qed.

Lemma list_insert_fold {A} l i (x : A) :
  list_insert i x l = <[i := x]> l.
Proof. done. Qed.

Lemma Is_true_eq (b : bool) : b ↔ b = true.
Proof. by case: b. Qed.

Lemma bool_decide_eq_x_x_true {A} (x : A) `{!Decision (x = x)} :
  bool_decide (x = x) = true.
Proof. by case_bool_decide.  Qed.


  Lemma StronglySorted_lookup_lt {A} R (l : list A) i j x y:
    StronglySorted R l → l !! i = Some x → l !! j = Some y → ¬ R y x → x ≠ y → (i < j)%nat.
  Proof.
    move => Hs Hi Hj HR Hneq. elim: Hs j i Hj Hi => // z {}l _ IH /Forall_forall Hall.
    case => /=.
    - case; first naive_solver. move => n [?]/= /(elem_of_list_lookup_2 _ _ _)?; subst. naive_solver.
    - move => n. case; first lia. move => n2 /= ??. apply lt_n_S. naive_solver.
  Qed.


  Definition list_subequiv {A} (ignored : list nat) (l1 l2 : list A) : Prop
    := ∀ i, length l1 = length l2 ∧ (i ∉ ignored → l1 !! i = l2 !! i).

  Global Instance list_subequiv_equiv A ig : Equivalence (list_subequiv (A:=A) ig).
  Proof.
    unfold list_subequiv. split => //.
    - move => ?? H i. move: (H i) => [-> ?]. split; first done. symmetry. naive_solver.
    - move => ??? H1 H2 i. move: (H1 i) => [-> H1i]. move: (H2 i) => [-> H2i].
      split; first done. etrans; first exact: H1i. naive_solver.
  Qed.

  Lemma subequiv_insert_in_l {A} (l1 l2 : list A) j x ig:
    j ∈ ig →
    list_subequiv ig (<[j := x]>l1) l2 ↔ list_subequiv ig l1 l2.
  Proof.
    unfold list_subequiv. move => ?. split => Hs i; move: (Hs i) => [<- H].
    - split; first by rewrite insert_length. move => ?.
      rewrite -H; last done. rewrite list_lookup_insert_ne; naive_solver.
    - split; first by rewrite insert_length. move => ?.
      rewrite list_lookup_insert_ne; naive_solver.
  Qed.

  Lemma subequiv_insert_in_r {A} (l1 l2 : list A) j x ig:
    j ∈ ig →
    list_subequiv ig l1 (<[j := x]>l2) ↔ list_subequiv ig l1 l2.
  Proof.
    move => ?.
    rewrite (symmetry_iff (list_subequiv _)) [in X in _ ↔ X](symmetry_iff (list_subequiv _)).
      by apply subequiv_insert_in_l.
  Qed.

  Lemma subequiv_insert_ne_l {A} (l1 l2 : list A) j x ig:
    (j < length l1)%nat → j ∉ ig →
    list_subequiv ig (<[j := x]>l1) l2 ↔ l2 !! j = Some x ∧ list_subequiv (j :: ig) l1 l2.
  Proof.
    move => ??. unfold list_subequiv. split.
    - move => Hs. move: (Hs j) => [<- <-]//. rewrite list_lookup_insert //. split => // i.
      rewrite insert_length. split => // Hi. move: (Hs i) => [? <-];[|set_solver].
      rewrite list_lookup_insert_ne //. set_solver.
    - rewrite insert_length. move => [? Hs] i. split; first by move: (Hs 0) => [? _]//.
      case: (decide (i = j)) => [->|?].
      + by rewrite list_lookup_insert.
      + rewrite list_lookup_insert_ne//. move: (Hs i) => [? H]// ?. apply H. set_solver.
  Qed.

  Lemma list_insert_subequiv {A} (l1 l2 : list A) j x1 :
    (j < length l1)%nat →
    <[j:=x1]>l1 = l2 ↔ l2 !! j = Some x1 ∧ list_subequiv [j] l1 l2.
  Proof.
    move => ?. split.
    - move => <-. rewrite list_lookup_insert // subequiv_insert_in_r //. set_solver.
    - move => [? Hsub]. apply list_eq => i. case: (decide (i = j)) => [->|?].
      + by rewrite list_lookup_insert.
      + rewrite list_lookup_insert_ne//. apply Hsub. set_solver.
  Qed.

  Lemma list_subequiv_split {A} (l1 l2 : list A) i :
    length l1 = length l2 →
    list_subequiv [i] l1 l2 ↔
    take i l1 = take i l2 ∧ drop (S i) l1 = drop (S i) l2.
  Proof.
    move => Hlen. split.
    - move => Hsub. split; apply list_eq => n; move: (Hsub n) => Hn; set_unfold.
      + destruct (decide (n < i)%nat).
        * rewrite !lookup_take; by naive_solver lia.
        * rewrite !lookup_ge_None_2 // take_length; lia.
      + rewrite !lookup_drop. apply Hsub. set_unfold. lia.
    - move => [Ht Hd] n. split; first done.
      move => ?. have ? : (n ≠ i) by set_solver.
      destruct (decide (n < i)%nat).
      + by rewrite -(lookup_take l1 i) // -(lookup_take l2 i) // Ht.
      + have ->:(n = (S i) + (n - (S i)))%nat by lia.
        by rewrite -!lookup_drop Hd.
  Qed.

Lemma default_last_cons {A} (x1 x2 y : A) l :
  default x1 (last (y :: l)) = default x2 (last (y :: l)).
Proof. elim: l y => //=. Qed.

Lemma list_lookup_length_default_last {A} (x : A) (l : list A) :
  (x :: l) !! length l = Some (default x (last l)).
Proof. elim: l x => //= a l IH x. rewrite IH. f_equal. destruct l => //. apply default_last_cons. Qed.


Reserved Notation "'[∧' 'map]' k ↦ x ∈ m , P"
           (at level 200, m at level 10, k, x at level 1, right associativity,
            format "[∧  map]  k ↦ x  ∈  m ,  P").
  Reserved Notation "'[∧' 'map]' x ∈ m , P"
           (at level 200, m at level 10, x at level 1, right associativity,
            format "[∧  map]  x  ∈  m ,  P").
  Notation "'[∧' 'map]' k ↦ x ∈ m , P" := (big_opM bi_and (λ k x, P) m) : bi_scope.
  Notation "'[∧' 'map]' x ∈ m , P" := (big_opM bi_and (λ _ x, P) m) : bi_scope.

Section bi_big_op.
  Context {PROP : bi}.
  Implicit Types P Q : PROP.
  Implicit Types Ps Qs : list PROP.
  Implicit Types A : Type.
  Section map.
  Context `{Countable K} {A : Type}.
  Implicit Types m : gmap K A.
  Implicit Types Φ Ψ : K → A → PROP.
  Lemma big_andM_empty Φ : ([∧ map] k↦y ∈ ∅, Φ k y) ⊣⊢ True.
  Proof. by rewrite big_opM_empty. Qed.
  (* Lemma big_andL_empty' P Φ : P ⊢ [∧ map] k↦y ∈ ∅, Φ k y. *)
  (* Proof. rewrite big_sepM_empty. by apply pure_intro. Qed. *)
  Lemma big_andM_insert Φ m i x :
    m !! i = None →
    ([∧ map] k↦y ∈ <[i:=x]> m, Φ k y) ⊣⊢ Φ i x ∧ [∧ map] k↦y ∈ m, Φ k y.
  Proof. apply big_opM_insert. Qed.
  End map.
End bi_big_op.


Lemma filter_nil_inv {A} P `{!∀ x, Decision (P x)} (l : list A):
  filter P l = [] ↔ (∀ x : A, x ∈ l → ¬ P x).
Proof.
  elim: l. 1: by rewrite filter_nil; set_solver.
  move => x l IH. rewrite filter_cons. case_decide; set_solver.
Qed.

Lemma length_filter_gt {A} P `{!∀ x, Decision (P x)} (l : list A) x:
  x ∈ l → P x →
  (0 < length (filter P l))%nat.
Proof. elim; move => *; rewrite filter_cons; case_decide; naive_solver lia. Qed.

Lemma length_filter_insert {A} P `{!∀ x, Decision (P x)} (l : list A) i x x':
  l !! i = Some x' →
  length (filter P (<[i:=x]>l)) =
  (length (filter P l) + (if bool_decide (P x) then 1 else 0) - (if bool_decide (P x') then 1 else 0))%nat.
Proof.
  elim: i l. move => [] //=??[->]. rewrite !filter_cons. by repeat (case_decide; case_bool_decide) => //=; lia.
  move => i IH [|? l]//=?. rewrite !filter_cons. case_decide => //=; rewrite IH // -minus_Sn_m //.
  repeat case_bool_decide => //; try lia. feed pose proof (length_filter_gt P l x') => //; try lia.
    by apply: elem_of_list_lookup_2.
Qed.

Lemma length_filter_replicate_True {A} P `{!∀ x, Decision (P x)} (x : A) len:
  P x → length (filter P (replicate len x)) = len.
Proof. elim: len => //=???. rewrite filter_cons. case_decide => //=. f_equal. naive_solver. Qed.

Lemma gmultiset_elem_of_equiv_empty {A} `{!EqDecision A} `{!Countable A} (X : gmultiset A):
  X = ∅ ↔ (∀ x, x ∉ X).
Proof. split; [set_solver|]. destruct (gmultiset_choose_or_empty X); naive_solver. Qed.

Lemma reshape_app {A} (ln1 ln2 : list nat) (l : list A) :
  reshape (ln1 ++ ln2) l = reshape ln1 (take (sum_list ln1) l) ++ reshape ln2 (drop (sum_list ln1) l).
Proof. elim: ln1 l => //= n ln1 IH l. rewrite take_take skipn_firstn_comm IH drop_drop. repeat f_equal; lia. Qed.
Lemma omap_app {A B} (f : A → option B) (s1 s2 : list A):
  omap f (s1 ++ s2) = omap f s1 ++ omap f s2.
Proof. elim: s1 => //. csimpl => ?? ->. case_match; naive_solver. Qed.
Lemma sum_list_with_take {A} f (l : list A) i:
   (sum_list_with f (take i l) ≤ sum_list_with f l)%nat.
Proof. elim: i l => /=. lia. move => ? IH [|? l2] => //=. move: (IH l2). lia.  Qed.
  Lemma omap_length_eq {A B C} (f : A → option B) (g : A → option C) (l : list A):
    (∀ i x, l !! i = Some x → const () <$> (f x) = const () <$> (g x)) →
    length (omap f l) = length (omap g l).
  Proof.
    elim: l => //; csimpl => x ? IH Hx. move: (Hx O x ltac:(done)) => /=?.
    do 2 case_match => //=; rewrite IH // => i ??; by apply: (Hx (S i)).
  Qed.


Definition is_power_of_two (n : nat) := ∃ m : nat, n = (2^m)%nat.
Arguments is_power_of_two : simpl never.
Typeclasses Opaque is_power_of_two.

Fixpoint Pos_factor2 (p : positive) : nat :=
  match p with
  | xO p => S (Pos_factor2 p)
  | _ => 0%nat
  end.

Definition factor2' (n : nat) : option nat :=
  match N.of_nat n with
  | N0 => None
  | Npos p => Some (Pos_factor2 p)
  end.
Definition factor2 (n : nat) (def : nat) : nat :=
  default def (factor2' n).

Definition keep_factor2 (n : nat) (def : nat) : nat :=
  default def (pow 2 <$> factor2' n).

Lemma Pos_pow_add_r a b c:
  (a ^ (b + c) = a ^ b * a ^ c)%positive.
Proof. zify. rewrite !Pos2Z.inj_pow Pos2Z.inj_add Z.pow_add_r; lia. Qed.

Lemma Pos_factor2_mult_xI a b:
  Pos_factor2 (a~1 * b) = Pos_factor2 b.
Proof.
  move: a. elim b => // p IH a. rewrite /= -/Pos.mul. f_equal.
  rewrite Pos.mul_xO_r [X in Pos_factor2 (_ + xO X) = _]Pos.mul_comm.
  rewrite -Pos.mul_xI_r Pos.mul_comm. apply IH.
Qed.

Lemma Pos_factor2_mult a b:
  Pos_factor2 (a * b) = (Pos_factor2 a + Pos_factor2 b)%nat.
Proof.
  elim: a b => // p IH b.
  - by rewrite Pos_factor2_mult_xI.
  - by rewrite Pos.mul_comm Pos.mul_xO_r /= Pos.mul_comm IH.
Qed.

Lemma Pos_factor2_pow n:
  Pos_factor2 (2^n)%positive = Pos.to_nat n.
Proof.
  elim: n => // p IH; rewrite ?Pos.xI_succ_xO -(Pos.add_diag p) -?Pos.add_succ_r -?Pos.add_1_r !Pos_pow_add_r !Pos_factor2_mult !IH /=; lia.
Qed.

Lemma Zdivide_mult_l n1 n2 a :
  ((n1 * n2 | a) → (n1 | a))%Z.
Proof. move => [? ->]. by apply Z.divide_mul_r, Z.divide_mul_l. Qed.

Lemma Zdivide_nat_pow a b c:
  ((b ≤ c)%nat → ((a ^ b)%nat | (a ^ c)%nat))%Z.
Proof.
  move => ?. apply: (Zdivide_mult_l _ (a^(c - b))%nat).
  by rewrite -Nat2Z.inj_mul -Nat.pow_add_r le_plus_minus_r.
Qed.

Lemma Pos_factor2_divide p :
  ((2 ^ Pos_factor2 p)%nat | Z.pos p)%Z.
Proof.
  elim: p => //=. by move => *; apply Z.divide_1_l.
  move => p IH. rewrite -plus_n_O Pos2Z.inj_xO Nat2Z.inj_add Z.add_diag. by apply Z.mul_divide_mono_l.
Qed.

Lemma factor2_divide n x :
  ((2 ^ factor2 n x)%nat | n)%Z.
Proof.
  rewrite /factor2/factor2'. rewrite -(nat_N_Z n). case_match => /=; first by apply Z.divide_0_r.
  apply Pos_factor2_divide.
Qed.

Lemma factor2'_pow n:
  factor2' (2^n)%nat = Some n.
Proof.
  rewrite /factor2'. destruct (N.of_nat (2 ^ n)) eqn:H.
  - exfalso. elim: n H => // /=. lia.
  - f_equal. move: p H. induction n as [|n IH].
    + move => p /= Hp. destruct p => //.
    + move => p Hp. destruct p.
      * exfalso. zify. rewrite Nat.pow_succ_r' in Hp. lia.
      * rewrite /=. f_equal. apply IH.
        zify. rewrite Nat.pow_succ_r' in Hp. lia.
      * exfalso. zify. rewrite Nat.pow_succ_r' in Hp. lia.
Qed.

Lemma factor2_pow n x:
  factor2 (2^n)%nat x = n.
Proof. by rewrite /factor2 factor2'_pow. Qed.

Lemma keep_factor2_0 n:
  keep_factor2 0 n = n.
Proof. done. Qed.

Lemma keep_factor2_mult n m o:
  n ≠ 0 → m ≠ 0 →
  keep_factor2 (m * n) o = keep_factor2 m o * keep_factor2 n o.
Proof.
  rewrite /keep_factor2 /factor2' => ??. destruct n,m => //=.
  rewrite -Nat.pow_add_r -Pos_factor2_mult. do 2 f_equal. lia.
Qed.

Lemma keep_factor2_neq_0 n x:
  n ≠ 0 →
  keep_factor2 n x ≠ 0.
Proof. move => ?. destruct n => //. rewrite /keep_factor2 /=. by apply Nat.pow_nonzero. Qed.

Lemma keep_factor2_is_power_of_two n x:
  is_power_of_two n →
  keep_factor2 n x = n.
Proof. move => [? ->]. by rewrite /keep_factor2 factor2'_pow. Qed.

Lemma keep_factor2_min_eq n m:
  is_power_of_two n →
  (n `min` keep_factor2 (m * n) n) = n.
Proof.
  move => ?. destruct (decide (m = 0)); first by subst; rewrite keep_factor2_0; lia.
  destruct (decide (n = 0)); first lia.
  rewrite keep_factor2_mult // (keep_factor2_is_power_of_two n) //.
  have ?: keep_factor2 m n ≠ 0 by apply keep_factor2_neq_0.
  destruct (keep_factor2 m n); lia.
Qed.

Lemma keep_factor2_min_1 n:
  (1 `min` keep_factor2 n 1)%nat = 1%nat.
Proof.
  rewrite /keep_factor2 /factor2'. destruct (N.of_nat n) => // /=.
  apply Nat.min_l. generalize (Pos_factor2 p) => k. induction k as [|k IH].
  done. rewrite Nat.pow_succ_r'. move: IH. generalize (2 ^ k) => j. lia.
Qed.

Lemma keep_factor2_twice n m:
  (keep_factor2 n (keep_factor2 n m)) = (keep_factor2 n m).
Proof. by destruct n. Qed.

(* Lemma mult_is_one_Z n m : 0 ≤ n → 0 ≤ m → n * m = 1 → n = 1 ∧ m = 1. *)
(* Proof. *)
(*   intros Hn Hm. *)
(*   move: (Z_of_nat_complete n Hn) => [i ->]. *)
(*   move: (Z_of_nat_complete m Hm) => [j ->]. *)
(*   move => HZ. assert (i * j = 1)%nat as H by lia. *)
(*   apply mult_is_one in H. lia. *)
(* Qed. *)

(* Lemma mult_is_mult_of_pow2_Z n1 n2 (m : nat): *)
(*   0 ≤ n1 → 0 ≤ n2 → n1 * n2 = 2 ^ m → ∃ (m1 m2 : nat), n1 = 2 ^ m1 ∧ n2 = 2 ^ m2. *)
(* Proof. *)
(*   revert n1 n2. induction m as [|m IH] => n1 n2 Hn1 Hn2. *)
(*   - rewrite Z.pow_0_r. move => /(mult_is_one_Z _ _ Hn1 Hn2) [-> ->]. by exists 0%nat, 0%nat. *)
(*   - assert (Z.of_nat (S m) = Z.succ m) as -> by lia. rewrite Z.pow_succ_r; last by lia. *)
(*     move => H. assert (2 | n1 * n2) as Hdiv. { rewrite H. apply Z.divide_mul_l, Z.divide_refl. } *)
(*     apply prime_mult in Hdiv; last by apply prime_2. *)
(*     destruct Hdiv as [Hdiv|Hdiv]; destruct Hdiv as [k ->]. *)
(*     + assert (k * 2 * n2 = 2 * (k * n2)) as Htmp by lia; rewrite Htmp in H; clear Htmp. *)
(*       apply Z.mul_cancel_l in H => //. apply IH in H; [ .. | lia | lia ]. *)
(*       destruct H as [m1 [m2 [-> ->]]]. exists (S m1), m2. split => //. *)
(*       rewrite Z.mul_comm -Z.pow_succ_r; last by lia. f_equal. lia. *)
(*     + assert (n1 * (k * 2) = 2 * (n1 * k)) as Htmp by lia; rewrite Htmp in H; clear Htmp. *)
(*       apply Z.mul_cancel_l in H => //. apply IH in H; [ .. | lia | lia ]. *)
(*       destruct H as [m1 [m2 [-> ->]]]. exists m1, (S m2). split => //. *)
(*       rewrite Z.mul_comm -Z.pow_succ_r; last by lia. f_equal. lia. *)
(* Qed. *)

Lemma divide_mult_2 n1 n2 : divide 2 (n1 * n2) → divide 2 n1 ∨ divide 2 n2.
  move => /Nat2Z_divide. rewrite Nat2Z.inj_mul. move => /(prime_mult _ prime_2).
  move => [H|H]; [left | right]; apply Z2Nat_divide in H; try lia.
  - rewrite Nat2Z.id in H. assert (Z.to_nat 2 = 2) as Heq by lia. by rewrite Heq in H.
  - rewrite Nat2Z.id in H. assert (Z.to_nat 2 = 2) as Heq by lia. by rewrite Heq in H.
Qed.

Lemma is_power_of_two_mult n1 n2:
  (is_power_of_two (n1 * n2)) ↔ (is_power_of_two n1 ∧ is_power_of_two n2).
Proof.
  rewrite /is_power_of_two. split.
  - move => [m Hm]. move: n1 n2 Hm. elim: m.
    + move => /= ?? /mult_is_one [->->]. split; by exists 0.
    + move => n IH n1 n2 H. rewrite Nat.pow_succ_r' in H.
      assert (divide 2 (n1 * n2)) as Hdiv. { exists (2 ^ n). lia. }
      apply divide_mult_2 in Hdiv as [[k ->]|[k ->]].
      * assert (k * n2 = 2 ^ n) as Hkn2 by lia.
        apply IH in Hkn2 as [[m ->] Hn2]. split => //.
        exists (S m). by rewrite mult_comm -Nat.pow_succ_r'.
      * assert (n1 * k = 2 ^ n) as Hn1k by lia.
        apply IH in Hn1k as [Hn1 [m ->]]. split => //.
        exists (S m). by rewrite mult_comm -Nat.pow_succ_r'.
  - move => [[m1 ->] [m2 ->]]. exists (m1 + m2). by rewrite Nat.pow_add_r.
Qed.

Lemma if_bool_decide_eq_branches {A} P `{!Decision P} (x : A) :
  (if bool_decide P then x else x) = x.
Proof. by case_bool_decide. Qed.

From iris.program_logic Require Import adequacy weakestpre.
Section adequacy.
Context `{!irisG Λ Σ}.
Implicit Types e : expr Λ.
Implicit Types P Q : iProp Σ.
Implicit Types Φ : val Λ → iProp Σ.
Implicit Types Φs : list (val Λ → iProp Σ).

Notation wptp s t := ([∗ list] ef ∈ t, WP ef @ s; ⊤ {{ fork_post }})%I.
Lemma wptp_step' s es1 t1 t2 κ κs σ1 σ2 Φs :
  step (es1 ++ t1,σ1) κ (t2, σ2) →
  state_interp σ1 (κ ++ κs) (length t1) -∗ ([∗ list] e;Φ∈es1; Φs, WP e @ s; ⊤ {{ Φ }}) -∗ wptp s t1 ==∗
  ∃ es2 t2', ⌜t2 = es2 ++ t2'⌝ ∗
  |={⊤}[∅]▷=> state_interp σ2 κs (length t2') ∗ ([∗ list] e;Φ∈es2;Φs, WP e @ s; ⊤ {{ Φ }}) ∗ wptp s t2'.
Proof.
  iIntros (Hstep) "Hσ He Ht".
  destruct Hstep as [e1' σ1' e2' σ2' efs t2' t3 Hstep]; simplify_eq/=.
  destruct (decide (length t2' < length es1)).
  - have [t3' [??]]: ∃ t3', es1 = t2' ++ e1' :: t3' ∧ t3 = t3' ++ t1; subst. {
      revert select (_ ++ _ = _ ++ _). rewrite -(take_drop (length t2') es1) -app_assoc.
      move => /app_inj_1[|->]; [rewrite take_length; lia|].
      have : 0 < length (drop (length t2') es1) by rewrite drop_length; lia.
      move: (drop (length t2') es1) => {l}[|e {}es1] /=;[lia|] => _ [-> <-]. eauto.
    }
    iExists (t2' ++ e2' :: t3'), (t1 ++ efs).
    iModIntro. iSplitR; first by rewrite -!app_assoc app_comm_cons.
    iDestruct (big_sepL2_app_inv_l with "He") as (Φs1 Φs2 ->) "[? He]".
    iDestruct (big_sepL2_cons_inv_l with "He") as (Φ Φs3 ->) "[He ?]".
    iMod (wp_step with "Hσ He") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)".
    iIntros "!>". rewrite Nat.add_comm app_length. iFrame.
  - have [t2'' [??]]: ∃ t2'', t1 = t2'' ++ e1' :: t3 ∧ t2' = es1 ++ t2''; subst. {
      revert select (_ ++ _ = _ ++ _). rewrite -(take_drop (length es1) t2') -app_assoc.
      move => /app_inj_1[|->]; rewrite take_length_le//; try lia. move => ->. eauto.
    }
    iExists es1, (t2'' ++ e2' :: t3 ++ efs); iSplitR; first by rewrite -!app_assoc app_comm_cons.
    iFrame "He". iDestruct "Ht" as "(Ht1 & He1 & Ht2)".
    iModIntro. iMod (wp_step with "Hσ He1") as "H"; first done.
    iIntros "!> !>". iMod "H" as "(Hσ & He2 & Hefs)". iIntros "!>".
    rewrite !app_length /= !app_length.
    replace (length t2'' + S (length t3 + length efs))
      with (length efs + (length t2'' + S (length t3))) by lia. iFrame.
Qed.

Lemma wptp_steps' s n es1 t1 κs κs' t2 σ1 σ2 Φs :
  nsteps n (es1 ++ t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗ ([∗ list] e;Φ∈es1; Φs, WP e @ s; ⊤ {{ Φ }}) -∗ wptp s t1
  ={⊤}[∅]▷=∗^n ∃ es2 t2',
    ⌜t2 = es2 ++ t2'⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    ([∗ list] e;Φ∈es2;Φs, WP e @ s; ⊤ {{ Φ }}) ∗ wptp s t2'.
Proof.
  revert es1 t1 κs κs' t2 σ1 σ2; simpl.
  induction n as [|n IH]=> es1 t1 κs κs' t2 σ1 σ2 /=.
  { inversion_clear 1; iIntros "???"; iExists es1, t1; iFrame; done. }
  iIntros (Hsteps) "Hσ He Ht". inversion_clear Hsteps as [|?? [t1' σ1']].
  rewrite -(assoc_L (++)).
  iMod (wptp_step' with "Hσ He Ht") as (e1' t1'' ?) ">H"; first eauto; simplify_eq.
  iIntros "!> !>". iMod "H" as "(Hσ & He & Ht)". iModIntro.
  by iApply (IH with "Hσ He Ht").
Qed.
Lemma wptp_strong_adequacy' Φs κs' s n es1 t1 κs t2 σ1 σ2 :
  nsteps n (es1 ++ t1, σ1) κs (t2, σ2) →
  state_interp σ1 (κs ++ κs') (length t1) -∗
  ([∗ list] e;Φ∈es1; Φs, WP e @ s; ⊤ {{ Φ }}) -∗
  wptp s t1 ={⊤}[∅]▷=∗^(S n) ∃ es2 t2',
    ⌜ t2 = es2 ++ t2' ⌝ ∗
    ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ ∗
    state_interp σ2 κs' (length t2') ∗
    ([∗ list] e;Φ∈es2;Φs, from_option Φ True (to_val e)) ∗
    ([∗ list] v ∈ omap to_val t2', fork_post v).
Proof.
  iIntros (Hstep) "Hσ He Ht". rewrite Nat_iter_S_r.
  iDestruct (wptp_steps' with "Hσ He Ht") as "Hwp"; first done.
  iApply (step_fupdN_wand with "Hwp").
  iDestruct 1 as (e2' t2' ?) "(Hσ & Hwp & Ht)"; simplify_eq/=.
  iMod (fupd_plain_keep_l ⊤
    ⌜ ∀ e2, s = NotStuck → e2 ∈ (e2' ++ t2') → not_stuck e2 σ2 ⌝%I
    (state_interp σ2 κs' (length t2') ∗ ([∗ list] e;Φ ∈ e2';Φs, WP e @ s; ⊤ {{ v, Φ v }}) ∗ wptp s t2')%I
    with "[$Hσ $Hwp $Ht]") as "(Hsafe&Hσ&Hwp&Hvs)".
  { iIntros "(Hσ & Hwp & Ht)" (e' -> He').
    move: He' => /elem_of_app[|]/(elem_of_list_split _ _)[?[?->]].
    - iDestruct (big_sepL2_app_inv_l with "Hwp") as (Φs1 Φs2 ->) "[? Hwp]".
      iDestruct (big_sepL2_cons_inv_l with "Hwp") as (Φ Φs3 ->) "[Hwp ?]".
      iMod (wp_not_stuck with "Hσ Hwp") as "$"; auto.
    - iDestruct "Ht" as "(_ & He' & _)". by iMod (wp_not_stuck with "Hσ He'"). }
  iApply step_fupd_fupd. iApply step_fupd_intro; first done. iNext.
  iExists _, _. iSplitL ""; first done. iFrame "Hsafe Hσ".
  iSplitL "Hwp".
  - iApply big_sepL2_fupd. iApply (big_sepL2_impl with "Hwp").
    iIntros "!#" (? e Φ ??) "Hwp".
    destruct (to_val e) as [v2|] eqn:He2'; last done.
    apply of_to_val in He2' as <-. iApply (wp_value_inv' with "Hwp").
  - clear Hstep. iInduction t2' as [|e t2'] "IH"; csimpl; first by iFrame.
    iDestruct "Hvs" as "[Hv Hvs]". destruct (to_val e) as [v|] eqn:He.
    + apply of_to_val in He as <-. iMod (wp_value_inv' with "Hv") as "$".
      by iApply "IH".
    + by iApply "IH".
Qed.
End adequacy.
Theorem wp_strong_adequacy' Σ Λ `{!invPreG Σ} es σ1 n κs t2 σ2 φ :
  (∀ `{Hinv : !invG Σ},
    ⊢ |={⊤}=> ∃
         (s: stuckness)
         (stateI : state Λ → list (observation Λ) → nat → iProp Σ)
         (Φs : list (val Λ → iProp Σ))
         (fork_post : val Λ → iProp Σ),
       let _ : irisG Λ Σ := IrisG _ _ Hinv stateI fork_post in
       stateI σ1 κs 0 ∗
       ([∗ list] e;Φ∈es;Φs, WP e @ s; ⊤ {{ Φ }}) ∗
       (∀ es' t2',
         (* es' is the final state of the initial threads, t2' the rest *)
         ⌜ t2 = es' ++ t2' ⌝ -∗
         (* If this is a stuck-free triple (i.e. [s = NotStuck]), then all
         threads in [t2] are not stuck *)
         ⌜ ∀ e2, s = NotStuck → e2 ∈ t2 → not_stuck e2 σ2 ⌝ -∗
         (* The state interpretation holds for [σ2] *)
         stateI σ2 [] (length t2') -∗
         (* If the initial threads are done, their post-condition [Φ] holds *)
         ([∗ list] e;Φ∈es';Φs, from_option Φ True (to_val e)) -∗
         (* For all threads that are done, their postcondition [fork_post] holds. *)
         ([∗ list] v ∈ omap to_val t2', fork_post v) -∗
         (* Under all these assumptions, and while opening all invariants, we
         can conclude [φ] in the logic. After opening all required invariants,
         one can use [fupd_intro_mask'] or [fupd_mask_weaken] to introduce the
         fancy update. *)
         |={⊤,∅}=> ⌜ φ ⌝)) →
  nsteps n (es, σ1) κs (t2, σ2) →
  (* Then we can conclude [φ] at the meta-level. *)
  φ.
Proof.
  intros Hwp ?.
  eapply (step_fupdN_soundness' _ (S (S n)))=> Hinv. rewrite Nat_iter_S.
  iMod Hwp as (s stateI Φ fork_post) "(Hσ & Hwp & Hφ)".
  iApply step_fupd_intro; [done|]; iModIntro.
  iApply step_fupdN_S_fupd. iApply (step_fupdN_wand with "[-Hφ]").
  { iApply (@wptp_strong_adequacy' _ _ (IrisG _ _ Hinv stateI fork_post) _ []
    with "[Hσ] Hwp"); eauto; by rewrite right_id_L. }
  iIntros "Hpost". iDestruct "Hpost" as (e2 t2' ->) "(? & ? & ? & ?)".
  iApply fupd_plain_mask_empty.
  iMod ("Hφ" with "[% //] [$] [$] [$] [$]"). done.
Qed.
