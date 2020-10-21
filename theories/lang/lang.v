From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap list.
From refinedc.lang Require Export base.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** Representation of a standard (8-bit) byte. *)
Section Byte.
  Definition bits_per_byte : Z := 8.

  Definition byte_modulus : Z :=
    Eval cbv in 2 ^ bits_per_byte.

  Record byte :=
    Byte {
      byte_val : Z;
      byte_constr : -1 < byte_val < byte_modulus;
    }.

  Global Instance byte_eq_dec : EqDecision byte.
  Proof.
    move => [b1 H1] [b2 H2]. destruct (decide (b1 = b2)) as [->|].
    - left. assert (H1 = H2) as ->; [|done]. apply proof_irrel.
    - right. naive_solver.
  Qed.
End Byte.

(** Representation of a type layout (byte size and alignment constraint). *)
Section Layout.
  Record layout :=
    Layout {
      ly_size : nat;
      ly_align_log : nat;
    }.

  Definition sizeof   (ly : layout) : nat := ly.(ly_size).
  Definition ly_align (ly : layout) : nat := 2 ^ ly.(ly_align_log).

  Global Instance layout_dec_eq : EqDecision layout.
  Proof. solve_decision. Defined.

  Global Instance layout_inhabited : Inhabited layout :=
    populate (Layout 0 0).

  Global Instance layout_countable : Countable layout.
  Proof.
    refine (inj_countable'
      (λ ly, (ly.(ly_size), ly.(ly_align_log)))
      (λ '(sz, a), Layout sz a) _); by intros [].
  Qed.

  Global Instance layout_le : SqSubsetEq layout := λ ly1 ly2,
    (ly1.(ly_size) ≤ ly2.(ly_size))%nat ∧
    (ly1.(ly_align_log) ≤ ly2.(ly_align_log))%nat.

  Global Instance layout_le_po : PreOrder layout_le.
  Proof.
    split => ?; rewrite /layout_le => *; repeat case_bool_decide => //; lia.
  Qed.

  Definition ly_offset (ly : layout) (n : nat) : layout := {|
    ly_size := ly.(ly_size) - n;
    (* Sadly we need to have the second argument to factor2 as we want
    that if l is aligned to x, then l + n * x is aligned to x for all n
    including 0. *)
    ly_align_log := ly.(ly_align_log) `min` factor2 n ly.(ly_align_log)
  |}.

  Definition ly_set_size (ly : layout) (n : nat) : layout := {|
    ly_size := n;
    ly_align_log := ly.(ly_align_log)
  |}.

  Definition ly_mult (ly : layout) (n : nat) : layout := {|
    ly_size := ly.(ly_size) * n;
    ly_align_log := ly.(ly_align_log)
  |}.

  Definition ly_with_align (sz : nat) (align : nat) : layout := {|
    ly_size := sz;
    ly_align_log := factor2 align 0
  |}.

  Definition layout_wf (ly : layout) : Prop := (ly_align ly | ly.(ly_size)).

  Lemma layout_wf_mod (ly : layout) :
    ly.(ly_size) `mod` ly_align ly = 0 → layout_wf ly.
  Proof.
    move => ?. apply Z.mod_divide => //. have ->: 0 = O by [].
    move => /Nat2Z.inj/Nat.pow_nonzero. lia.
  Qed.

  Class LayoutWf (ly : layout) : Prop := layout_wf_wf : layout_wf ly.

  (* Class required because the combinators of layout are made typeclass opaque
     later, so TCEq does not work. *)
  Class LayoutEq (ly1 ly2 : layout) : Prop := layout_eq : ly1 = ly2.
End Layout.

Arguments ly_size : simpl never.
Arguments sizeof _ /.
(*Arguments ly_align_log : simpl never.*)
Arguments ly_align : simpl never.

Typeclasses Opaque layout_le ly_offset ly_set_size ly_mult ly_with_align.

Hint Extern 0 (LayoutWf _) => refine (layout_wf_mod _ _); done : typeclass_instances.
Hint Extern 0 (LayoutWf _) => unfold LayoutWf; done : typeclass_instances.
Hint Extern 0 (LayoutEq _ _) => exact: eq_refl : typeclass_instances.

(** Representation of an integer type (size and signedness). *)
Section IntType.
  Definition signed := bool.

  Record int_type :=
    IntType {
      it_byte_size_log : nat;
      it_signed : signed;
    }.

  Definition bytes_per_int (it : int_type) : nat :=
    2 ^ it.(it_byte_size_log).

  Lemma bytes_per_int_gt_0 it : bytes_per_int it > 0.
  Proof.
    rewrite /bytes_per_int. move: it => [log ?] /=.
    rewrite Z2Nat_inj_pow. assert (0 < 2%nat ^ log); last lia.
    apply Z.pow_pos_nonneg; lia.
  Qed.

  Definition bits_per_int (it : int_type) : Z :=
    bytes_per_int it * bits_per_byte.

  Definition int_modulus (it : int_type) : Z :=
    2 ^ bits_per_int it.

  Definition int_half_modulus (it : int_type) : Z :=
    2 ^ (bits_per_int it - 1).

  Lemma int_modulus_twice_half_modulus (it : int_type) :
    int_modulus it = 2 * int_half_modulus it.
  Proof.
    rewrite /int_modulus /int_half_modulus.
    rewrite -[X in X * _]Z.pow_1_r -Z.pow_add_r; try f_equal; try lia.
    rewrite /bits_per_int /bytes_per_int.
    apply Z.le_add_le_sub_l. rewrite Z.add_0_r.
    rewrite Z2Nat_inj_pow.
    assert (0 < 2%nat ^ it_byte_size_log it * bits_per_byte); last lia.
    apply Z.mul_pos_pos; last (rewrite /bits_per_byte; lia).
    apply Z.pow_pos_nonneg; lia.
  Qed.

  (* Minimal representable integer. *)
  Definition min_int (it : int_type) : Z :=
    if it.(it_signed) then - int_half_modulus it else 0.

  (* Maximal representable integer. *)
  Definition max_int (it : int_type) : Z :=
    (if it.(it_signed) then int_half_modulus it else int_modulus it) - 1.

  Lemma min_int_le_0 (it : int_type) : min_int it ≤ 0.
  Proof.
    have ? := bytes_per_int_gt_0 it. rewrite /min_int /int_half_modulus.
    destruct (it_signed it) => //. trans (- 2 ^ 7) => //.
    rewrite -Z.opp_le_mono. apply Z.pow_le_mono_r => //.
    rewrite /bits_per_int /bits_per_byte. lia.
  Qed.

  Lemma max_int_ge_127 (it : int_type) : 127 ≤ max_int it.
  Proof.
    have ? := bytes_per_int_gt_0 it.
    rewrite /max_int /int_modulus /int_half_modulus.
    rewrite /bits_per_int /bits_per_byte.
    have ->: (127 = 2 ^ 7 - 1) by []. apply Z.sub_le_mono => //.
    destruct (it_signed it); apply Z.pow_le_mono_r; lia.
  Qed.

  Global Instance int_elem_of_it : ElemOf Z int_type :=
    λ z it, min_int it ≤ z ≤ max_int it.

  Definition it_layout (it : int_type) :=
    Layout (bytes_per_int it) it.(it_byte_size_log).

  Definition i8  := IntType 0 true.
  Definition u8  := IntType 0 false.
  Definition i16 := IntType 1 true.
  Definition u16 := IntType 1 false.
  Definition i32 := IntType 2 true.
  Definition u32 := IntType 2 false.
  Definition i64 := IntType 3 true.
  Definition u64 := IntType 3 false.

  (* hardcoding 64bit pointers for now *)
  Definition bytes_per_addr_log : nat := 3%nat.
  Definition bytes_per_addr : nat := (2 ^ bytes_per_addr_log)%nat.

  Definition intptr_t  := IntType bytes_per_addr_log false.
  Definition uintptr_t := IntType bytes_per_addr_log true.

  Definition size_t  := intptr_t.
  Definition ssize_t := uintptr_t.
  Definition bool_it := u8.
End IntType.

Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

Definition block_id := Z.

Definition loc : Set := block_id * Z.
Bind Scope loc_scope with loc.

Inductive mbyte : Set :=
| MByte (b : byte)
| MPtrFrag (l : loc) (n : nat)
| MPoison.

Definition val : Set := list mbyte.
Bind Scope val_scope with val.

Inductive lock_state := WSt | RSt (n : nat).

Definition heap := gmap loc (lock_state * mbyte).

Definition blocks := gset block_id.



Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.
Definition offset_loc (l : loc) (ly : layout) (z : Z) : loc := (l +ₗ ly.(ly_size) * z).
Notation "l 'offset{' ly '}ₗ' z" := (offset_loc l%L ly z%Z)
  (at level 50, format "l  'offset{' ly '}ₗ'  z", left associativity) : loc_scope.

Definition aligned_to (l : loc) (n : nat) : Prop := (n | l.2).
Notation "l `aligned_to` n" := (aligned_to l n) (at level 50) : stdpp_scope.
Definition has_layout_loc (l : loc) (ly : layout) : Prop := l `aligned_to` ly_align ly.
Notation "l `has_layout_loc` n" := (has_layout_loc l n) (at level 50) : stdpp_scope.
Definition has_layout_val (v : val) (ly : layout) : Prop := length v = ly.(ly_size).
Notation "v `has_layout_val` n" := (has_layout_val v n) (at level 50) : stdpp_scope.

Arguments aligned_to : simpl never.
(* Arguments aligned_to_log : simpl never. *)
Arguments has_layout_loc : simpl never.
Arguments has_layout_val : simpl never.
Typeclasses Opaque aligned_to has_layout_loc has_layout_val.


(*** Definitions of the language *)
Definition label := string. (* make TC opaque and implement countable and eqdicision *)
Definition var_name := string.

Inductive op_type : Set :=
| IntOp (i : int_type) | PtrOp.

(* see http://compcert.inria.fr/doc/html/compcert.cfrontend.Cop.html#binary_operation *)
Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | XorOp | ShlOp
| ShrOp | EqOp | NeOp | LtOp | GtOp | LeOp | GeOp
(* Ptr is the second argument and pffset the first *)
| PtrOffsetOp (ly : layout).

Inductive un_op : Set :=
| NotBoolOp | NotIntOp | NegOp | CastOp (ot : op_type).
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Inductive expr :=
| Var (x : var_name)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| Deref (o : order) (ly : layout) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| Concat (es : list expr)
| SkipE (e : expr)
| StuckE (* stuck expression *)
.

(** Note that there is no explicit Fork. Instead the initial state can
contain multiple threads (like a processor which has a fixed number of
hardware threads). *)
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
(* m: map from values of e to indices into bs, def: default *)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ly : layout) (e1 e2 : expr) (s : stmt)
| Call (ret : var_name) (f : expr) (args : list expr) (s : stmt)
| SkipS (s : stmt)
| StuckS (* stuck statement *)
| ExprS (e : expr) (s : stmt)
.

Arguments Switch _%E _%E _%E.
Arguments Call _%E _%E _%E _%E.

Record function := {
  f_args : list (var_name * layout);
  f_local_vars : list (var_name * layout);
  (* TODO should we add this: f_ret : layout; ?*)
  f_code : gmap label stmt;
  f_init : label;
}.

(* TODO: put both function and bytes in the same heap or make pointers disjoint (current version is wrong)*)
Record state := {
  st_heap: heap;
  st_used_blocks: blocks;
  st_fntbl: gmap loc function;
}.

Record runtime_function := {
  (* locations of args and local vars are substitued in the body *)
  rf_fn : function;
  (* locations in the stack frame (locations of arguments and local
  vars allocated on Call, need to be freed by Return) *)
  rf_locs: list (loc * layout);
  (* current statement *)
  rf_stmt: stmt;
}.

Record continuation := {
  c_rfn: runtime_function;
  (* name of the variable in which the result should be returned *)
  c_rvar: var_name;
  (* TODO should we add this: c_rlayout: layout; ?*)
}.

Record thread_state := {
  ts_rfn: runtime_function;
  ts_conts: list continuation;
}.

(* values for statements *)
Record stmt_val := {
  sv_fn : function;
  sv_locs: list (loc * layout);
  sv_val: val;
}.

Implicit Type (l : loc) (e : expr) (v : val) (sz : nat) (h : heap) (σ : state) (ly : layout) (s : stmt) (sgn : signed) (rf : runtime_function) (ts : thread_state) (co : continuation).

(*** Relating val to logical values *)
(* we use little endian *)
Fixpoint val_to_int_go v : option Z :=
match v with
| [] => Some 0
| (MByte b)::v' => z ← val_to_int_go v'; Some (byte_modulus * z + b.(byte_val))
| _ => None
end.
Definition val_to_int (v : val) (it : int_type) : option Z :=
  if decide (length v = bytes_per_int it) then
    z ← val_to_int_go v; if it.(it_signed) && bool_decide (int_half_modulus it ≤ z) then Some (z - int_modulus it) else Some z
  else None.

Program Fixpoint val_of_int_go (n : Z) sz : val :=
  match sz return _ with
  | O => []
  | S sz' => (MByte ({| byte_val := (n `mod` byte_modulus) |}))::(val_of_int_go (n / byte_modulus) sz')
  end.
Next Obligation. move => n. have [] := Z_mod_lt n byte_modulus => //*. lia. Qed.

Definition val_of_int (z : Z) (it : int_type) : option val :=
  if bool_decide (z ∈ it) then
    let p := if bool_decide (z < 0) then z + int_modulus it else z in
    Some (val_of_int_go p (bytes_per_int it))
  else
    None.

Lemma val_of_int_go_length z sz :
  length (val_of_int_go z sz) = sz.
Proof. elim: sz z => //= ? IH ?. by f_equal. Qed.

Lemma val_to_of_int_go z sz :
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
Proof. rewrite /val_of_int => Hv. case_bool_decide => //. simplify_eq. by rewrite val_of_int_go_length. Qed.

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

Fixpoint val_to_loc_go (v : val) (pos : nat) (l : loc) : option loc :=
  match v with
  | (MPtrFrag l' pos')::v' =>
    if bool_decide (pos = pos' ∧ l = l') then
      if bool_decide (pos = bytes_per_addr - 1)%nat then (if v' is [] then Some l else None) else val_to_loc_go v' (S pos) l
    else None
  | _ => None
  end.
Definition val_to_loc (v : val) : option loc :=
  match v with
  | (MPtrFrag l 0)::v' => val_to_loc_go v' 1%nat l
  | _ => None
  end.
Definition val_of_loc (l : loc) : val := MPtrFrag l <$> seq 0 bytes_per_addr.

Lemma val_to_of_loc l :
  val_to_loc (val_of_loc l) = Some l.
Proof. simpl. by case_decide. Qed.

Lemma val_of_to_loc v l :
  val_to_loc v = Some l → v = val_of_loc l.
Proof.
  destruct v => //=; case_match => //; case_match => //.
  repeat (match goal with
  | |- context [ val_to_loc_go ?v _ _ ] => destruct v
          end => //=;
                  case_match => //; repeat (case_decide; subst => //=)).
  by case_match => // [[->]].
Qed.

Definition i2v (n : Z) (it : int_type) : val := default [MPoison] (val_of_int n it).

Definition val_of_bool (b : bool) : val := i2v (Z_of_bool b) bool_it.

Lemma val_of_int_bool b it:
  val_of_int (Z_of_bool b) it = Some (i2v (Z_of_bool b) it).
Proof.
  have [|? Hv] := val_of_int_is_some it (Z_of_bool b); last by rewrite /i2v Hv.
  rewrite /elem_of /int_elem_of_it.
  have ? := min_int_le_0 it. have ? := max_int_ge_127 it.
  split; destruct b => /=; lia.
Qed.

Lemma i2v_bool_length b it:
  length (i2v (Z_of_bool b) it) = bytes_per_int it.
Proof. by have /val_of_int_length -> := val_of_int_bool b it. Qed.
Lemma i2v_bool_Some b it:
  val_to_int (i2v (Z_of_bool b) it) it = Some (Z_of_bool b).
Proof. apply val_to_of_int. apply val_of_int_bool. Qed.

Arguments val_to_int : simpl never.
Arguments val_of_int : simpl never.
Arguments val_to_loc : simpl never.
Arguments val_of_loc : simpl never.
Typeclasses Opaque val_to_loc val_of_loc val_to_int val_of_int val_of_bool.


Lemma val_to_int_bool b :
  val_to_int (val_of_bool b) bool_it = Some (Z_of_bool b).
Proof. by destruct b. Qed.

(*** Properties of layouts and alignment *)
Lemma ly_align_log_ly_align_eq_iff ly1 ly2:
  ly_align_log ly1 = ly_align_log ly2 ↔ ly_align ly1 = ly_align ly2.
Proof. rewrite /ly_align. split; first naive_solver. move => /Nat.pow_inj_r. lia. Qed.

Lemma ly_align_ly_with_align m n :
  ly_align (ly_with_align m n) = keep_factor2 n 1.
Proof. rewrite /ly_with_align/keep_factor2/factor2. by destruct (factor2' n). Qed.

Lemma ly_align_ly_offset ly n :
  ly_align (ly_offset ly n) = (ly_align ly `min` keep_factor2 n (ly_align ly))%nat.
Proof.
  rewrite /ly_align/keep_factor2/=/factor2. destruct (factor2' n) as [n'|] => /=; last by rewrite !Nat.min_id.
  destruct (decide (ly_align_log ly ≤ n'))%nat;[rewrite !min_l|rewrite !min_r]; try lia;
    apply Nat.pow_le_mono_r; lia.
Qed.

Lemma ly_align_ly_set_size ly n:
  ly_align (ly_set_size ly n) = ly_align ly.
Proof. done. Qed.

Lemma ly_with_align_aligned_to l m n:
  l `aligned_to` n →
  is_power_of_two n →
  l `has_layout_loc` ly_with_align m n.
Proof. move => ??. by rewrite /has_layout_loc ly_align_ly_with_align keep_factor2_is_power_of_two. Qed.

Lemma has_layout_loc_trans l ly1 ly2 :
  l `has_layout_loc` ly2 → (ly1.(ly_align_log) ≤ ly2.(ly_align_log))%nat → l `has_layout_loc` ly1.
Proof. rewrite /has_layout_loc/aligned_to => Hl ?. etrans;[|by apply Hl]. by apply Zdivide_nat_pow. Qed.

Lemma has_layout_loc_1 l ly:
  ly_align ly = 1%nat →
  l `has_layout_loc` ly.
Proof. rewrite /has_layout_loc =>  ->. by apply Z.divide_1_l. Qed.

Lemma has_layout_ly_offset l (n : nat) ly:
  l `has_layout_loc` ly →
  (l +ₗ n) `has_layout_loc` ly_offset ly n.
Proof.
  move => Hl. apply Z.divide_add_r.
  - apply: has_layout_loc_trans => //. rewrite {1}/ly_align_log/=. destruct n; lia.
  - rewrite/ly_offset. destruct n;[by subst;apply Z.divide_0_r|]. etrans;[apply Zdivide_nat_pow, Min.le_min_r|]. by apply factor2_divide.
Qed.

Lemma has_layout_loc_ly_mult_offset l ly n:
  layout_wf ly →
  l `has_layout_loc` ly_mult ly (S n) →
  (l +ₗ ly_size ly) `has_layout_loc` ly_mult ly n.
Proof. move => ??. rewrite /ly_mult. by apply Z.divide_add_r. Qed.


Lemma aligned_to_offset l n off :
  l `aligned_to` n → (n | off) → (l +ₗ off) `aligned_to` n.
Proof. apply Z.divide_add_r. Qed.

Lemma aligned_to_add l (n : nat) x:
  (l +ₗ x * n) `aligned_to` n ↔ l `aligned_to` n.
Proof.
  unfold aligned_to. destruct l as [? a] => /=. rewrite Z.add_comm.
  split.
  - apply: Z.divide_add_cancel_r. by apply Z.divide_mul_r.
  - apply Z.divide_add_r. by apply Z.divide_mul_r.
Qed.

Lemma aligned_to_mult_eq l n1 n2 off:
  l `aligned_to` n2 → (l +ₗ off) `aligned_to` (n1 * n2) → (n2 | off).
Proof.
  unfold aligned_to. destruct l as [? a] => /= ??. apply: Z.divide_add_cancel_r => //.
  apply: (Zdivide_mult_l _ n1). by rewrite Z.mul_comm -Nat2Z.inj_mul.
Qed.

(*** Helper functions for accessing the heap *)

Fixpoint heap_at_go l v flk h : Prop :=
  match v with
  | [] => True
  | b::v' => (∃ lk, h !! l = Some (lk, b) ∧ flk lk) ∧ heap_at_go (l +ₗ 1) v' flk h
  end.

Definition heap_at l ly v flk h : Prop :=
  l `has_layout_loc` ly ∧ v `has_layout_val` ly ∧ heap_at_go l v flk h.

Definition heap_block_free h l : Prop := ∀ i, h !! (l +ₗ i) = None.

Fixpoint heap_upd l v flk h : heap :=
  match v with
  | b::v' => partial_alter (λ m, Some (flk (fst <$> m), b)) l (heap_upd (l +ₗ 1) v' flk h)
  | [] => h
  end.

Fixpoint heap_upd_list ls vs flk h : heap :=
  match ls, vs with
  | l::ls', v::vs' => heap_upd l v flk (heap_upd_list ls' vs' flk h)
  | _, _ => h
  end.

Fixpoint heap_free l n h : heap :=
  match n with
  | O => h
  | S n' => delete l (heap_free (l +ₗ 1) n' h)
  end.

Fixpoint heap_free_list ls h : heap :=
  match ls with
  | (l, ly)::ls' => heap_free l ly.(ly_size) (heap_free_list ls' h)
  | _ => h
  end.

Definition update_stmt ts s := {|
  ts_conts := ts.(ts_conts);
  ts_rfn := {| rf_fn := ts.(ts_rfn).(rf_fn); rf_stmt := s; rf_locs := ts.(ts_rfn).(rf_locs) |};
|}.

Definition heap_fmap f σ := {|
  st_heap := f σ.(st_heap);
  st_fntbl := σ.(st_fntbl);
  st_used_blocks := σ.(st_used_blocks);
|}.

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Definition stmt_to_val (ts : thread_state) : option stmt_val :=
  match ts.(ts_rfn).(rf_stmt), ts.(ts_conts) with
  | Return (Val v), [] => Some {| sv_fn := ts.(ts_rfn).(rf_fn); sv_locs := ts.(ts_rfn).(rf_locs); sv_val := v |}
  | _,_ => None
  end.

Definition stmt_of_val (sv : stmt_val) : thread_state := {|
  ts_rfn := {| rf_stmt := Return (Val sv.(sv_val));
               rf_locs := sv.(sv_locs);
               rf_fn := sv.(sv_fn); |};
  ts_conts := [];
|}.



(*** Evaluation of operations *)
(** Checks that the location [l] is allocated on the heap [h] *)
Definition valid_ptr l h : Prop :=
  is_Some (h !! l).
(** Checks whether location [l] is a weak valid pointer in heap [h].
[Some true] means [l] is a valid in bounds pointer, [Some false] means
[l] is a end of block pointer, [None] means [l] is not a valid pointer. *)
Definition weak_valid_ptr l h : option bool :=
  if decide (valid_ptr l h) then
    Some true
  else if decide (valid_ptr (l +ₗ -1) h ∧ ¬valid_ptr l h) then
    Some false
  else None.
(** Checks equality between [l1] and [l2]. See
http://compcert.inria.fr/doc/html/compcert.common.Values.html#Val.cmplu_bool
*)
Definition ptr_eq l1 l2 h : option bool :=
  eob1 ← weak_valid_ptr l1 h;
  eob2 ← weak_valid_ptr l2 h;
  if decide (l1.1 = l2.2) then
    Some (bool_decide (l1 = l2))
  else
    if eob1 || eob2 then None else Some false.

(* evaluation can be non-deterministic for comparing pointers *)
(* TODO: implement *)
Inductive eval_bin_op : bin_op → op_type → op_type → heap → val → val → val → Prop :=
| AddOpPI v1 v2 h o l:
    val_to_loc v1 = Some l →
    val_to_int v2 size_t = Some o →
    eval_bin_op AddOp PtrOp (IntOp size_t) h v1 v2 (val_of_loc (l +ₗ o))
| PtrOffsetOpIP v1 v2 h o l ly it:
    val_to_int v1 it = Some o →
    val_to_loc v2 = Some l →
    (* TODO: should we have an alignment check here? *)
    0 ≤ o →
    eval_bin_op (PtrOffsetOp ly) (IntOp it) PtrOp h v1 v2 (val_of_loc (l offset{ly}ₗ o))
| EqOpPNull v1 v2 h l v:
    val_to_loc v1 = Some l →
    val_to_int v2 size_t = Some 0 →
    (* TODO ( see below ): Should we really hard code i32 here because of C? *)
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp h v1 v2 v
| NeOpPNull v1 v2 h l v:
    val_to_loc v1 = Some l →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp h v1 v2 v
| EqOpNullNull v1 v2 h v:
    val_to_int v1 size_t = Some 0 →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp h v1 v2 v
| NeOpNullNull v1 v2 h v:
    val_to_int v1 size_t = Some 0 →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp h v1 v2 v
| EqOpPP v1 v2 h l1 l2 v b:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    ptr_eq l1 l2 h = Some b →
    i2v (Z_of_bool b) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp h v1 v2 v
| NeOpPP v1 v2 h l1 l2 v b:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    ptr_eq l1 l2 h = Some b →
    i2v (Z_of_bool (negb b)) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp h v1 v2 v
| RelOpII op v1 v2 h n1 n2 it b:
    match op with
    | EqOp => Some (bool_decide (n1 = n2))
    | NeOp => Some (bool_decide (n1 ≠ n2))
    | LtOp => Some (bool_decide (n1 < n2))
    | GtOp => Some (bool_decide (n1 > n2))
    | LeOp => Some (bool_decide (n1 <= n2))
    | GeOp => Some (bool_decide (n1 >= n2))
    | _ => None
    end = Some b →
    val_to_int v1 it = Some n1 →
    val_to_int v2 it = Some n2 →
    (* TODO: What is the right int type of the result here? C seems to
    use i32 but maybe we don't want to hard code that. *)
    eval_bin_op op (IntOp it) (IntOp it) h v1 v2 (i2v (Z_of_bool b) i32)
(* This defines checked versions of the arithmetic operations which
are UB if the result is out of bounds for it. *)
| ArithOpII op v1 v2 h n1 n2 it n v:
    match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    (* we need to take `quot` and `rem` here for the correct rounding
    behavior, i.e. rounding towards 0 (instead of `div` and `mod`,
    which round towards floor)*)
    | DivOp => if n2 is 0 then None else Some (n1 `quot` n2)
    | ModOp => if n2 is 0 then None else Some (n1 `rem` n2)
    (* TODO: Figure out if these are the operations we want *)
    | AndOp => Some (Z.land n1 n2)
    | OrOp => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    | ShlOp => Some (n1 ≪ n2)
    | ShrOp => Some (n1 ≫ n2)
    | _ => None
    end = Some n →
    val_to_int v1 it = Some n1 →
    val_to_int v2 it = Some n2 →
    val_of_int n it = Some v →
    eval_bin_op op (IntOp it) (IntOp it) h v1 v2 v
.


Inductive eval_un_op : un_op → op_type → heap → val → val → Prop :=
| CastOpII itt its h vs vt n:
    val_to_int vs its = Some n →
    val_of_int n itt = Some vt →
    eval_un_op (CastOp (IntOp itt)) (IntOp its) h vs vt
| CastOpPP h vs vt l:
    val_to_loc vs = Some l →
    val_of_loc l = vt →
    eval_un_op (CastOp PtrOp) PtrOp h vs vt
| NegOpI it h vs vt n:
    val_to_int vs it = Some n →
    val_of_int (-n) it = Some vt →
    eval_un_op NegOp (IntOp it) h vs vt
.

(*** Evaluation of Expressions *)

Inductive expr_step : expr → state → list Empty_set → expr → state → list expr → Prop :=
| SkipES v σ:
    expr_step (SkipE (Val v)) σ [] (Val v) σ []
| UnOpS op v σ v' ot:
    eval_un_op op ot σ.(st_heap) v v' →
    expr_step (UnOp op ot (Val v)) σ [] (Val v') σ []
| BinOpS op v1 v2 σ v' ot1 ot2:
    eval_bin_op op ot1 ot2 σ.(st_heap) v1 v2 v' →
    expr_step (BinOp op ot1 ot2 (Val v1) (Val v2)) σ [] (Val v') σ []
| DerefS o v l ly v' σ:
    let start_st st := ∃ n, st = if o is Na2Ord then RSt (S n) else RSt n in
    let end_st st := match o, st with
                     | Na1Ord, Some (RSt n) => RSt (S n)
                     | Na2Ord, Some (RSt (S n)) => RSt n
                     | ScOrd, Some st => st
                     (* unreachable *)
                     |  _, _ => WSt end in
    let end_expr := if o is Na1Ord then Deref Na2Ord ly (Val v) else Val v' in
    val_to_loc v = Some l →
    heap_at l ly v' start_st σ.(st_heap) →
    expr_step (Deref o ly (Val v)) σ [] end_expr (heap_fmap (heap_upd l v' end_st) σ) []
(* TODO: look at CAS and see whether it makes sense. Also allow
comparing pointers? (see lambda rust) *)
(* corresponds to atomic_compare_exchange_strong, see https://en.cppreference.com/w/c/atomic/atomic_compare_exchange *)
| CasFailS l1 l2 vo ve σ z1 z2 v1 v2 v3 it:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, ∃ n, st = RSt n) σ.(st_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, st = RSt 0%nat) σ.(st_heap) →
    val_to_int vo it = Some z1 →
    val_to_int ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool false)) (heap_fmap (heap_upd l2 vo (λ _, RSt 0%nat)) σ) []
| CasSucS l1 l2 it vo ve σ z1 z2 v1 v2 v3:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, st = RSt 0%nat) σ.(st_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, ∃ n, st = RSt n) σ.(st_heap) →
    val_to_int vo it = Some z1 →
    val_to_int ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 = z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool true)) (heap_fmap (heap_upd l1 v3 (λ _, RSt 0%nat)) σ) []
| ConcatS vs σ:
    expr_step (Concat (Val <$> vs)) σ [] (Val (mjoin vs)) σ []
(* no rule for StuckE *)
.

(*** evaluation contexts *)
(** for expressions*)
Inductive ectx_item :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| DerefCtx (o : order) (l : layout)
| CASLCtx (ot : op_type) (e2 e3 : expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| ConcatCtx (vs : list val) (es : list expr)
| SkipECtx
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | UnOpCtx op ot => UnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => BinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => BinOp op ot1 ot2 (Val v1) e
  | DerefCtx o l => Deref o l e
  | CASLCtx ot e2 e3 => CAS ot e e2 e3
  | CASMCtx ot v1 e3 => CAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => CAS ot (Val v1) (Val v2) e
  | ConcatCtx vs es => Concat ((Val <$> vs) ++ e :: es)
  | SkipECtx => SkipE e
  end.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Val <$> vl1) ++ e1 :: el1 = (Val <$> vl2) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_eq_false vl1 vl2 e el :
  to_val e = None → Val <$> vl1 = (Val <$> vl2) ++ e :: el → False.
Proof.
  move => He. elim: vl2 vl1 => [[]//=*|v vl2 IH [|??]?]; csimpl in *; simplify_eq; eauto.
Qed.

(** Statements *)
Inductive stmt_ectx :=
(* Assignment is evalutated right to left, otherwise we need to split contexts *)
| AssignRCtx (o : order) (ly : layout) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ly : layout) (v2 : val) (s : stmt)
| ReturnCtx
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| CallLCtx (r : var_name) (args : list expr) (s : stmt)
| CallRCtx (r : var_name) (f : val) (vl : list val) (el : list expr) (s : stmt)
| ExprSCtx (s : stmt)
.

Definition stmt_fill (Ki : stmt_ectx) (e : expr) : stmt :=
  match Ki with
  | AssignRCtx o ly e1 s => Assign o ly e1 e s
  | AssignLCtx o ly v2 s => Assign o ly e (Val v2) s
  | ReturnCtx => Return e
  | SwitchCtx it m bs def => Switch it e m bs def
  | CallLCtx r args s => Call r e args s
  | CallRCtx r f vl el s => Call r (Val f) ((Val <$> vl) ++ e :: el) s
  | ExprSCtx s => ExprS e s
  end.

(*** Language instance for expressions *)

Lemma of_to_val e v : to_val e = Some v → Val v = e.
Proof. move: e => []; naive_solver. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  expr_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move: Ki1 Ki2 => [ ^ Ki1] [ ^Ki2] He1 He2 HEQ //; simplify_eq; try done.
  apply list_expr_val_eq_inv in HEQ; [ by destruct HEQ as (-> & _ & ->) | done | done ].
Qed.

Lemma expr_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  expr_step (fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki; inversion 1; simplify_eq; decompose_Forall_hyps; simplify_option_eq; try by eauto.
  apply not_eq_None_Some; intros ?; by eapply list_expr_val_eq_false.
Qed.

Lemma expr_lang_mixin : EctxiLanguageMixin Val to_val fill_item expr_step.
Proof.
  split => //; eauto using of_to_val, val_stuck, fill_item_inj, fill_item_val, fill_item_no_val_inj, expr_ctx_step_val.
Qed.
Canonical Structure expr_ectxi_lang := EctxiLanguage expr_lang_mixin.
Canonical Structure expr_ectx_lang := EctxLanguageOfEctxi expr_ectxi_lang.
Canonical Structure expr_lang := LanguageOfEctx expr_ectx_lang.

(*** Substitution *)
Fixpoint subst (x : var_name) (v : val) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | UnOp op ot e => UnOp op ot (subst x v e)
  | BinOp op ot1 ot2 e1 e2 => BinOp op ot1 ot2 (subst x v e1) (subst x v e2)
  | Deref o l e => Deref o l (subst x v e)
  | CAS ly e1 e2 e3 => CAS ly (subst x v e1) (subst x v e2) (subst x v e3)
  | Concat el => Concat (subst x v <$> el)
  | SkipE e => SkipE (subst x v e)
  | StuckE => StuckE
  end.

Fixpoint subst_l (xs : list var_name) (vs : list val) (e : expr)  : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst x v (subst_l xs' vs' e)
  | _, _ => e
  end.

Fixpoint subst_stmt (xs : list var_name) (vs : list val) (s : stmt) : stmt :=
  match s with
  | Goto b => Goto b
  | Return e => Return (subst_l xs vs e)
  | Switch it e m' bs def => Switch it (subst_l xs vs e) m' (subst_stmt xs vs <$> bs) (subst_stmt xs vs def)
  | Assign o ly e1 e2 s => Assign o ly (subst_l xs vs e1) (subst_l xs vs e2) (subst_stmt xs vs s)
  | Call ret f args s =>
    (* TODO: remove ret from xs*)
    Call ret (subst_l xs vs f) (subst_l xs vs <$> args) (subst_stmt xs vs s)
  | SkipS s => SkipS (subst_stmt xs vs s)
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_l xs vs e) (subst_stmt xs vs s)
  end.

Definition subst_function (xs : list var_name) (vs : list val) (f : function) : function := {|
  f_code := (subst_stmt xs vs) <$> f.(f_code);
  f_args := f.(f_args); f_init := f.(f_init); f_local_vars := f.(f_local_vars);
|}.

(*** Evaluation of statements *)
Inductive stmt_step : thread_state → state → list Empty_set → thread_state → state → list thread_state → Prop :=
| StmtExprS ts σ σ' Ks e e' os efs:
    ts.(ts_rfn).(rf_stmt) = stmt_fill Ks e →
    prim_step e σ os e' σ' efs →
    stmt_step ts σ os (update_stmt ts (stmt_fill Ks e')) σ' []
| AssignS (o : order) ts σ s v1 v2 l v' ly:
    let start_st st := st = if o is Na2Ord then WSt else RSt 0%nat in
    let end_st _ := if o is Na1Ord then WSt else RSt 0%nat in
    let end_val  := if o is Na1Ord then v' else v2 in
    let end_stmt := if o is Na1Ord then Assign Na2Ord ly (Val v1) (Val v2) s else s in
    ts.(ts_rfn).(rf_stmt) = Assign o ly (Val v1) (Val v2) s →
    val_to_loc v1 = Some l →
    v2 `has_layout_val` ly →
    heap_at l ly v' start_st σ.(st_heap) →
    stmt_step ts σ [] (update_stmt ts end_stmt) (heap_fmap (heap_upd l end_val end_st) σ) []
| SwitchS ts σ v n m bs s def it :
    ts.(ts_rfn).(rf_stmt) = Switch it (Val v) m bs def →
    val_to_int v it = Some n →
    (∀ i : nat, m !! n = Some i → is_Some (bs !! i)) →
    stmt_step ts σ [] (update_stmt ts $ default def (i ← m !! n; bs !! i)) σ []
| GotoS ts σ b s :
    ts.(ts_rfn).(rf_stmt) = Goto b →
    ts.(ts_rfn).(rf_fn).(f_code) !! b = Some s →
    stmt_step ts σ [] (update_stmt ts s) σ []
| ReturnS ts σ v co cs:
    ts.(ts_rfn).(rf_stmt) = Return (Val v) →
    ts.(ts_conts) = co :: cs →
    stmt_step ts σ []
     (* substitute the return value for rvar *)
     (update_stmt {| ts_conts := cs; ts_rfn := co.(c_rfn) |} (subst_stmt [co.(c_rvar)] [v] co.(c_rfn).(rf_stmt)))
     (* deallocate the stack *)
     (heap_fmap (heap_free_list ts.(ts_rfn).(rf_locs)) σ) []
| CallS lsa lsv ts σ vf vs s co f rf fn fn' h' h'' ret ub':
    ts.(ts_rfn).(rf_stmt) = Call ret (Val vf) (Val <$> vs) s →
    val_to_loc vf = Some f →
    σ.(st_fntbl) !! f = Some fn →
    length lsa = length fn.(f_args) →
    length lsv = length fn.(f_local_vars) →
    (* substitute the variables in fn with the corresponding locations *)
    fn' = subst_function (fn.(f_args).*1 ++ fn.(f_local_vars).*1) (val_of_loc <$> (lsa ++ lsv)) fn →
    (* check the layout of the arguments *)
    Forall2 has_layout_val vs fn.(f_args).*2 →
    (* ensure that ls points to free blocks *)
    Forall (heap_block_free σ.(st_heap)) lsa →
    Forall (heap_block_free σ.(st_heap)) lsv →
    (* ensure that ls blocks are unused *)
    Forall (λ l, l.1 ∉ σ.(st_used_blocks)) lsa →
    Forall (λ l, l.1 ∉ σ.(st_used_blocks)) lsv →
    (* ensure that locations are aligned *)
    Forall2 has_layout_loc lsa fn.(f_args).*2 →
    Forall2 has_layout_loc lsv fn.(f_local_vars).*2 →
    (* ensure that the blocks in ls are disjoint *)
    NoDup (lsa ++ lsv).*1 →
    (* initialize the local vars to poison *)
    heap_upd_list lsv ((λ p, replicate p.2.(ly_size) MPoison) <$> fn.(f_local_vars)) (λ _, RSt 0%nat) σ.(st_heap) = h' →
    (* initialize the arguments with the supplied values *)
    heap_upd_list lsa vs (λ _, RSt 0%nat) h' = h'' →
    σ.(st_used_blocks) ∪ list_to_set (lsa ++ lsv).*1 = ub' →
    rf = {| rf_fn := fn'; rf_locs := zip lsa fn.(f_args).*2 ++ zip lsv fn.(f_local_vars).*2; rf_stmt := Goto fn'.(f_init); |} →
    co = {| c_rfn := (update_stmt ts s).(ts_rfn); c_rvar := ret |} →
    stmt_step ts σ [] {| ts_conts := co::ts.(ts_conts); ts_rfn := rf |}
              {| st_heap:= h''; st_fntbl := σ.(st_fntbl); st_used_blocks := ub' |} []
| SkipSS ts σ s :
    ts.(ts_rfn).(rf_stmt) = SkipS s →
    stmt_step ts σ [] (update_stmt ts s) σ []
| ExprSS ts σ s v:
    ts.(ts_rfn).(rf_stmt) = ExprS (Val v) s →
    stmt_step ts σ [] (update_stmt ts s) σ []
(* no rule for StuckS *)
.

(*** Language instance for statements *)
Lemma stmt_to_of_val sv : stmt_to_val (stmt_of_val sv) = Some sv.
Proof. move: sv => [???]. by cbn. Qed.

Lemma stmt_of_to_val ts sv : stmt_to_val ts = Some sv → stmt_of_val sv = ts.
Proof.
  destruct ts as [rf [|??]]; destruct rf as [?? s]; destruct s as [|[] |  |  | | | |]; cbn => //?.
  by simplify_eq.
Qed.

Lemma stmt_val_stuck ts σ κ ts' σ' efs : stmt_step ts σ κ ts' σ' efs → stmt_to_val ts = None.
Proof.
  move sv: (stmt_to_val ts) => [] // /stmt_of_to_val <-;
    inversion_clear 1; cbn in * => //. destruct Ks => //; simpl in *. simplify_eq.
  exfalso. apply: val_irreducible H1. by eexists.
Qed.

Lemma stmt_lang_mixin : LanguageMixin stmt_of_val stmt_to_val stmt_step.
Proof.
  split; eauto using stmt_to_of_val, stmt_of_to_val, stmt_val_stuck.
Qed.
Canonical Structure stmt_lang := Language stmt_lang_mixin.

(*** General lemmata *)
Lemma Z_of_bool_true b :
  Z_of_bool b ≠ 0 ↔ b = true.
Proof. destruct b; naive_solver. Qed.

Lemma Z_of_bool_false b :
  Z_of_bool b = 0 ↔ b = false.
Proof. destruct b; naive_solver. Qed.

Lemma shift_loc_assoc l n n' : l +ₗ n +ₗ n' = l +ₗ (n + n').
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0 l : l +ₗ 0 = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_assoc_nat l (n n' : nat) : l +ₗ n +ₗ n' = l +ₗ (n + n')%nat.
Proof. rewrite /shift_loc /=. f_equal. lia. Qed.
Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
Proof. destruct l as [b o]. rewrite /shift_loc /=. f_equal. lia. Qed.

Lemma shift_loc_S l n: l +ₗ S n = (l +ₗ 1%nat +ₗ n).
Proof. by rewrite shift_loc_assoc_nat. Qed.

Lemma shift_loc_inj1 l1 l2 n : l1 +ₗ n = l2 +ₗ n → l1 = l2.
Proof. destruct l1, l2. case => -> ?. f_equal. lia. Qed.

Instance shift_loc_inj2 l : Inj (=) (=) (shift_loc l).
Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
Proof. done. Qed.

Lemma offset_loc_0 l ly : l offset{ly}ₗ 0 = l.
Proof. rewrite /offset_loc/=. have -> : ly_size ly * 0 = 0 by lia. apply shift_loc_0. Qed.

Lemma offset_loc_S l ly n : l offset{ly}ₗ S n = (l offset{ly}ₗ 1) offset{ly}ₗ n.
Proof. rewrite /offset_loc/shift_loc/=. destruct l => /=. f_equal. lia. Qed.

Lemma offset_loc_1 l ly : l offset{ly}ₗ 1%nat = (l +ₗ ly.(ly_size)).
Proof. rewrite /offset_loc/shift_loc/=. destruct l => /=. f_equal. lia. Qed.

Lemma offset_loc_sz1 ly l n : ly.(ly_size) = 1%nat → l offset{ly}ₗ n = l +ₗ n.
Proof. rewrite /offset_loc => ->. f_equal. lia. Qed.


Lemma stmt_to_val_non_ret ts s :
  (if s is Return (Val v) then False else True) →
  stmt_to_val (update_stmt ts s) = None.
Proof. destruct s as [ |e| | | | | |] => //. by destruct e. Qed.

Lemma stmt_fill_inj Ks1 Ks2 e1 e2 :
  to_val e1 = None → to_val e2 = None → stmt_fill Ks1 e1 = stmt_fill Ks2 e2 →
  Ks1 = Ks2 ∧ e1 = e2.
Proof.
  move => He1 He2.
  destruct Ks1 as [ | | | | | r1 f1 vl1 el1 s1| ],
           Ks2 as [ | | | | | r2 f2 vl2 el2 s2| ] => //= *; simplify_eq => //.
  by have [|||->[->->]] := (list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2).
Qed.

Lemma update_stmt_update ts s1 s2:
  update_stmt (update_stmt ts s1) s2 = update_stmt ts s2.
Proof. f_equal. Qed.

Lemma update_stmt_id ts:
  update_stmt ts ts.(ts_rfn).(rf_stmt) = ts.
Proof. by move: ts => [[]]. Qed.

Lemma heap_at_go_inj_val l h v v' flk1 flk2:
  length v = length v' →
  heap_at_go l v flk1 h → heap_at_go l v' flk2 h → v = v'.
Proof.
  elim: v v' l. by move => [|??] // ? [[]].
  move => b v IH [|b' v'] //= l [?] [[?[??]]?] [[?[??]]?]; simplify_eq. f_equal.
  by apply: IH.
Qed.

Lemma heap_at_go_inj_val'  l h v v' flk1 flk2 ly:
  v `has_layout_val` ly →
  heap_at_go l v flk1 h → heap_at l ly v' flk2 h → v = v'.
Proof. move => ??[_[??]]. apply: heap_at_go_inj_val => //. congruence. Qed.

Lemma heap_at_inj_val l ly h v v' flk1 flk2:
  heap_at l ly v flk1 h → heap_at l ly v' flk2 h → v = v'.
Proof. move => [_ [Hv1 H1]] [_ [Hv2 H2]]. apply: heap_at_go_inj_val => //. congruence. Qed.

Lemma heap_fresh_blocks n (ub : gset Z) lys :
  length lys = n →
  ∃ ls, length ls = n ∧ Forall (λ l : loc, l.1 ∉ ub) ls ∧ NoDup ls.*1 ∧ Forall2 has_layout_loc ls lys.
Proof.
  eexists ((λ x, (x, 0)) <$> fresh_list n ub). rewrite fmap_length fresh_list_length.
  split_and! => //.
  - apply Forall_forall => l. move => /elem_of_list_fmap[?[->?]]/=.
      by apply: fresh_list_is_fresh.
  - rewrite -list_fmap_compose. eapply (NoDup_proper _ (fresh_list n ub)); last by apply NoDup_fresh_list.
    elim: (fresh_list n ub); naive_solver.
  - rewrite Forall2_fmap_l. apply Forall2_true; last by rewrite fresh_list_length.
    move => ?? /=. by apply Z.divide_0_r.
Qed.

Lemma heap_upd_ext h l v f1 f2:
  (∀ x, f1 x = f2 x) →
  heap_upd l v f1 h = heap_upd l v f2 h.
Proof. move => Hext. elim: v l => //= ?? IH ?. rewrite IH. apply: partial_alter_ext => ??. by rewrite Hext. Qed.

Lemma heap_upd_lookup_lt l n bl h flk:
  n > 0 →
  heap_upd (l +ₗ n) bl flk h !! l = h !! l.
Proof.
  elim: bl n => // b bl IH /= n Hn. rewrite shift_loc_assoc.
  rewrite lookup_partial_alter_ne //.
  - apply IH. lia.
  - rewrite /shift_loc. destruct l => /= [[]]. lia.
Qed.

Lemma heap_upd_lookup_ne l v h i l' flk:
  l'.1 ≠ l.1 →
  heap_upd l' v flk h !! (l +ₗ i) = h !! (l +ₗ i).
Proof.
  elim: v l' => // b bl IH l' Hne /=.
  rewrite lookup_partial_alter_ne //.
  - by apply IH.
  - by destruct l, l' => [[]].
Qed.

Lemma heap_upd_heap_at_id l v flk flk' h:
  heap_at_go l v flk' h →
  (∀ st, flk (Some st) = st) →
  heap_upd l v flk h = h.
Proof.
  elim: v l => //= b v IH l [[lk[Hlk ?]]?] Hflk. rewrite IH //.
  apply: partial_alter_self_alt'. by rewrite Hlk Hflk.
Qed.


Lemma heap_block_free_upd_list ls vs h l flk:
  heap_block_free h l → l.1 ∉ ls.*1 →
  heap_block_free (heap_upd_list ls vs flk h) l.
Proof.
  rewrite /heap_block_free.
  elim: ls vs => // l' ls IH [|v vs] // Hfree; csimpl => Hl i.
  rewrite heap_upd_lookup_ne; set_solver.
Qed.

Lemma heap_block_free_free_list h l ls:
  heap_block_free h l →
  heap_block_free (heap_free_list ls h) l.
Proof.
  elim: ls l => // -[l [sz ?]] ls IH l' Hf /= o. unfold ly_size.
  elim: sz l. move => ?. by apply IH.
  move => sz IH2 l /=. apply lookup_delete_None. naive_solver.
Qed.

Lemma heap_free_delete h l l' n :
  delete l (heap_free l' n h) = heap_free l' n (delete l h).
Proof. revert l'. induction n as [|n IH]=> l' //=. by rewrite delete_commute IH. Qed.

Lemma heap_free_list_app ls1 ls2 h:
  heap_free_list (ls1 ++ ls2) h = heap_free_list ls1 (heap_free_list ls2 h).
Proof. by elim: ls1 => //= [[??]] ? ->. Qed.

Instance mbyte_inhabited : Inhabited mbyte := populate (MPoison).
Instance val_inhabited : Inhabited val := _.
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance stmt_inhabited : Inhabited stmt := populate (Goto "a").
Instance function_inhabited : Inhabited function := populate {| f_args := []; f_local_vars := []; f_code := ∅; f_init := "" |}.

Canonical Structure mbyteO := leibnizO mbyte.
Canonical Structure functionO := leibnizO function.
Canonical Structure locO := leibnizO loc.
Canonical Structure layoutO := leibnizO layout.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.

(*** Tests *)

Example simpl_subst :
  subst_stmt (["y"; "x"]) [[MPoison; MPoison]; [MPoison]] (Return (BinOp AddOp PtrOp PtrOp (Var "x") (Var "y"))) = Return (BinOp AddOp PtrOp PtrOp (Val [MPoison]) (Val [MPoison; MPoison])).
Proof. simpl. done. Abort.
