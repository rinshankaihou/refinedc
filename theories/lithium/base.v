From Coq Require Export ssreflect.
From stdpp Require Export sorting.
From iris.algebra Require Export big_op.
From Coq.ZArith Require Import Znumtheory.
From stdpp Require Import gmap list.
From iris.program_logic Require Import weakestpre.
From iris.bi Require Import derived_laws.
Import interface.bi derived_laws.bi.
From iris.proofmode Require Import tactics.
From stdpp Require Import natmap.

Global Unset Program Cases.
Global Set Keyed Unification.

Typeclasses Opaque is_Some.
(* This is necessary since otherwise keyed unification unfolds these definitions *)
Global Opaque rotate_nat_add rotate_nat_sub.

Typeclasses Opaque Z.divide Z.modulo Z.div Z.shiftl Z.shiftr.
Arguments min : simpl nomatch.

Arguments Z.testbit : simpl never.
Arguments Z.shiftl : simpl never.
Arguments Z.shiftr : simpl never.
Arguments N.shiftl : simpl never.
Arguments N.shiftr : simpl never.
Arguments Pos.shiftl : simpl never.
Arguments Pos.shiftr : simpl never.

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

Ltac get_head e :=
  lazymatch e with
  | ?h _ => get_head constr:(h)
  | _    => constr:(e)
  end.

Definition Z_of_bool (b : bool) : Z :=
  if b then 1 else 0.
Typeclasses Opaque Z_of_bool.

Lemma Z_of_bool_true b: Z_of_bool b ≠ 0 ↔ b = true.
Proof. destruct b; naive_solver. Qed.

Lemma Z_of_bool_false b: Z_of_bool b = 0 ↔ b = false.
Proof. destruct b; naive_solver. Qed.

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

Lemma zip_with_nil_inv' {A B C : Type} (f : A → B → C) (l1 : list A) (l2 : list B) :
  length l1 = length l2 → zip_with f l1 l2 = [] → l1 = [] ∧ l2 = [].
Proof.
  move => Hlen /zip_with_nil_inv [] H; rewrite H /= in Hlen;
  split => //; by apply nil_length_inv.
Qed.

Lemma entails_eq {PROP : bi} (P1 P2 : PROP) :
  P1 = P2 → P1 -∗ P2.
Proof. move => ->. reflexivity. Qed.

Section list_to_map.
  Context `{FinMap K M}.

  Lemma list_to_map_app {A} (l1 l2 : list (K * A)):
    list_to_map (M := M A) (l1 ++ l2) = list_to_map l1 ∪ list_to_map l2.
  Proof using Type*.
    elim: l1 => /=. { by rewrite left_id. }
    move => [??] ? IH /=. by rewrite IH insert_union_l.
  Qed.
End list_to_map.

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

Lemma replicate_O {A} (x : A) n:
  n = 0%nat -> replicate n x = [].
Proof. by move => ->. Qed.

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

Lemma StronglySorted_lookup_le {A} R (l : list A) i j x y:
  StronglySorted R l → l !! i = Some x → l !! j = Some y → (i ≤ j)%nat → x = y ∨ R x y.
Proof.
  move => Hsorted. elim: Hsorted i j => // z {}l ? IH Hall [|?] [|?]//=???; simplify_eq; try lia.
  - by left.
  - right. by apply: (Forall_lookup_1 _ _ _ _ Hall).
  - apply: IH => //. lia.
Qed.


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
Typeclasses Opaque list_subequiv.

  Global Instance list_subequiv_equiv A ig : Equivalence (list_subequiv (A:=A) ig).
  Proof.
    unfold list_subequiv. split => //.
    - move => ?? H i. move: (H i) => [-> ?]. split; first done. symmetry. naive_solver.
    - move => ??? H1 H2 i. move: (H1 i) => [-> H1i]. move: (H2 i) => [-> H2i].
      split; first done. etrans; first exact: H1i. naive_solver.
  Qed.

  Lemma subequiv_nil_l {A} (l : list A) ig:
    list_subequiv ig [] l ↔ l = [].
  Proof. split => Hs; destruct l => //. by move: (Hs 0) => [??]. Qed.

  Lemma subequiv_nil_r {A} (l : list A) ig:
    list_subequiv ig l [] ↔ l = [].
  Proof. split => Hs; destruct l => //. by move: (Hs 0) => [??]. Qed.

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

Section big_op.
Context {PROP : bi}.
Implicit Types P Q : PROP.
Implicit Types Ps Qs : list PROP.
Implicit Types A : Type.

(** ** Big ops over lists *)
Section sep_list.
  Context {A : Type}.
  Implicit Types l : list A.
  Implicit Types Φ Ψ : nat → A → PROP.

  Lemma big_sepL_insert l i x Φ:
    (i < length l)%nat →
 (([∗ list] k↦v ∈ <[i:=x]> l, Φ k v) ⊣⊢ Φ i x ∗ ([∗ list] k↦v ∈ l, if bool_decide (k = i) then emp else Φ k v)).
Proof.
  intros Hl.
  destruct (lookup_lt_is_Some_2 l i Hl) as [y Hy].
  rewrite -(take_drop_middle l i y) // insert_app_r_alt take_length_le // ?Nat.sub_diag /=; [|lia..].
  rewrite !big_sepL_app /= take_length_le ?Nat.add_0_r ?bool_decide_true ?left_id //; [|lia].
  rewrite assoc (comm _ _ (Φ _ _)) -assoc.
  do 2 f_equiv; apply big_sepL_proper => ?? /(lookup_lt_Some _ _ _) Hin ; rewrite bool_decide_false //.
  - rewrite take_length in Hin. lia.
  - rewrite drop_length in Hin. lia.
Qed.

Lemma big_sepL_impl' {B} Φ (Ψ : _ → B → _) (l1 : list A) (l2 : list B) :
    length l1 = length l2 →
    ([∗ list] k↦x ∈ l1, Φ k x) -∗
    □ (∀ k x1 x2, ⌜l1 !! k = Some x1⌝ -∗ ⌜l2 !! k = Some x2⌝ -∗ Φ k x1 -∗ Ψ k x2) -∗
    [∗ list] k↦x ∈ l2, Ψ k x.
  Proof.
    iIntros (Hlen) "Hl #Himpl".
    iInduction l1 as [|x1 l1] "IH" forall (Φ Ψ l2 Hlen); destruct l2 => //=; simpl in *.
    iDestruct "Hl" as "[Hx1 Hl]". iSplitL "Hx1". by iApply "Himpl".
    iApply ("IH" $! (Φ ∘ S) (Ψ ∘ S) l2 _ with "[] Hl").
    iIntros "!>" (k y1 y2 ?) "Hl2 /= ?".
      by iApply ("Himpl" with "[] [Hl2]").
      Unshelve. lia.
  Qed.
End sep_list.

  Lemma big_sepL2_impl' {A B C D} (Φ : _ → _ → _ → PROP) (Ψ : _ → _ → _ → _) (l1 : list A) (l2 : list B) (l1' : list C) (l2' : list D)  `{!BiAffine PROP} :
    length l1 = length l1' → length l2 = length l2' →
    ([∗ list] k↦x;y ∈ l1; l2, Φ k x y) -∗
    □ (∀ k x1 x2 y1 y2, ⌜l1 !! k = Some x1⌝ -∗ ⌜l2 !! k = Some x2⌝ -∗ ⌜l1' !! k = Some y1⌝ -∗  ⌜l2' !! k = Some y2⌝ -∗ Φ k x1 x2 -∗ Ψ k y1 y2) -∗
    [∗ list] k↦x;y ∈ l1';l2', Ψ k x y.
  Proof.
    iIntros (Hlen1 Hlen2) "Hl #Himpl".
    rewrite !big_sepL2_alt. iDestruct "Hl" as (Hl1) "Hl".
    iSplit. { iPureIntro. congruence. }
    iApply (big_sepL_impl' with "Hl"). { rewrite !zip_with_length. lia. }
    iIntros "!>" (k [x1 x2] [y1 y2]).
    rewrite !lookup_zip_with_Some.
    iDestruct 1 as %(?&?&?&?).
    iDestruct 1 as %(?&?&?&?). simplify_eq. destruct_and!.
    by iApply "Himpl".
  Qed.
End big_op.

Lemma vec_cast {A} n (v : vec A n) m:
  n = m → ∃ v' : vec A m, vec_to_list v = vec_to_list v'.
Proof.
  elim: v m => [|??? IH] [|m']// ?.
  - by eexists vnil.
  - have [|??]:= IH m'. { lia. }
    eexists (vcons _ _) => /=. by f_equal.
Qed.


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
Proof. zify. rewrite Z.pow_add_r; lia. Qed.

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

Lemma keep_factor2_leq (n m : nat):
  is_power_of_two n → (n | m) →
  n ≤ keep_factor2 m n.
Proof.
  move => ? [o ->]. destruct (decide (o = 0)); first by subst; rewrite keep_factor2_0; lia.
  destruct (decide (n = 0)); first lia.
  rewrite keep_factor2_mult // (keep_factor2_is_power_of_two n) //.
  have ?: keep_factor2 o n ≠ 0 by apply keep_factor2_neq_0.
  destruct (keep_factor2 o n); lia.
Qed.

Lemma keep_factor2_min_eq (n m : nat):
  is_power_of_two n → (n | m) →
  (n `min` keep_factor2 m n) = n.
Proof. move => ??. apply: Nat.min_l. by apply: keep_factor2_leq. Qed.

Lemma keep_factor2_min_1 n:
  1 `min` keep_factor2 n 1 = 1.
Proof.
  rewrite /keep_factor2 /factor2'. destruct (N.of_nat n) => // /=.
  apply Nat.min_l. generalize (Pos_factor2 p) => k. induction k as [|k IH] => //.
  rewrite Nat.pow_succ_r'. lia.
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

Lemma Z_distr_mul_sub_1 a b:
  (a * b - b = (a - 1) * b)%Z.
Proof. nia. Qed.

Lemma mult_le_compat_r_1 m p:
  (1 ≤ m)%nat → (p ≤ m * p)%nat.
Proof. nia. Qed.


Lemma if_bool_decide_eq_branches {A} P `{!Decision P} (x : A) :
  (if bool_decide P then x else x) = x.
Proof. by case_bool_decide. Qed.

(* from https://mattermost.mpi-sws.org/iris/pl/dcktjjjpsiycmrieyh74bzoagr *)
Ltac solve_sep_entails :=
  try (apply equiv_entails; split);
  iIntros;
  repeat iMatchHyp (fun H P =>
    lazymatch P with
    | (_ ∗ _)%I => iDestruct H as "[??]"
    | (∃ _, _)%I => iDestruct H as (?) "?"
    end);
  eauto with iFrame.

Inductive TCFalse : Prop :=.
Existing Class TCFalse.

Notation TCUnless P := (TCIf P TCFalse TCTrue).

Inductive TCExists {A} (P : A → Prop) : list A → Prop :=
| TCExists_cons_hd x l : P x → TCExists P (x :: l)
| TCExists_cons_tl x l: TCExists P l → TCExists P (x :: l).
Existing Class TCExists.
Existing Instance TCExists_cons_hd | 10.
Existing Instance TCExists_cons_tl | 20.
Global Hint Mode TCExists ! ! ! : typeclass_instances.

Lemma TCExists_Exists {A} (P : A → Prop) l :
  TCExists P l ↔ Exists P l.
Proof.
  elim: l. { split; inversion 1. }
  move => ?? IH. split; inversion 1; simplify_eq; constructor => //; by apply IH.
Qed.

(* Binary representation of bounded integers. *)

Lemma pos_bounded_iff_bits k n :
  (0 ≤ k → 0 ≤ n → n < 2^k ↔ ∀ l, k ≤ l → Z.testbit n l = false)%Z.
Proof.
  move => Hk Hn.
  destruct (decide (n = 0)) as [->|].
  - setoid_rewrite Z.bits_0. split => // ?. by apply: Z.pow_pos_nonneg.
  - split.
    + move => /Z.log2_lt_pow2 Hb l Hl.
      apply Z.bits_above_log2 => //. lia.
    + move => Hl.
      destruct (decide (n < 2^k)%Z) => //.
      have : Z.testbit n (Z.log2 n) = false.
      { apply Hl, Z.log2_le_pow2; lia. }
      rewrite Z.bit_log2 //. lia.
Qed.

Lemma bounded_iff_bits k n :
  (0 ≤ k → -2^k ≤ n < 2^k ↔
    ∀ l, k ≤ l → Z.testbit n l = bool_decide (n < 0))%Z.
Proof.
  move => Hk.
  case_bool_decide; last by rewrite -pos_bounded_iff_bits; lia.
  have -> : (n = - Z.abs n)%Z by lia.
  split.
  + move => [? _] l Hl.
    rewrite Z.bits_opp ?negb_true_iff; last lia.
    eapply pos_bounded_iff_bits => //; lia.
  + move => He.
    split; last by etrans; [|apply: Z.pow_pos_nonneg]; lia.
    rewrite -Z.opp_le_mono.
    suff : (Z.abs n - 1 < 2 ^ k)%Z by lia.
    apply pos_bounded_iff_bits; [lia..|] => l Hl.
    rewrite -negb_true_iff -Z.bits_opp; last lia.
    by apply: He.
Qed.

(** Z.lnot (bitwise negation) for unsigned integers with [bits] bits. *)
Definition Z_lunot (bits n : Z) :=
  (Z.lnot n `mod` 2 ^ bits)%Z.
Typeclasses Opaque Z_lunot.

Lemma Z_lunot_spec bits n k:
  (0 ≤ k < bits)%Z → Z.testbit (Z_lunot bits n) k = negb (Z.testbit n k).
Proof.
  move => [? ?].
  by rewrite Z.mod_pow2_bits_low ?Z.lnot_spec.
Qed.

Lemma Z_lunot_range bits n:
  (0 ≤ bits → 0 ≤ Z_lunot bits n < 2 ^ bits)%Z.
Proof.
  move => ?.
  apply: Z.mod_pos_bound.
  by apply: Z.pow_pos_nonneg.
Qed.


(** What follows are random things where is is not clear where to put them*)
