From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap list.
From refinedc.lang Require Export base byte layout int_type.
Set Default Proof Using "Type".

Open Scope Z_scope.

(** * Locations *)

Declare Scope loc_scope.
Delimit Scope loc_scope with L.
Open Scope loc_scope.

(** Physical address. *)
Definition addr := Z.

(** Allocation identifier (unique to an allocation). *)
Definition alloc_id := Z.
Definition dummy_alloc_id : alloc_id := 0.

(** Memory location. *)
Definition loc : Set := option alloc_id * addr.
Bind Scope loc_scope with loc.

Definition shift_loc (l : loc) (z : Z) : loc := (l.1, l.2 + z).
Notation "l +ₗ z" := (shift_loc l%L z%Z)
  (at level 50, left associativity) : loc_scope.
Typeclasses Opaque shift_loc.

Definition offset_loc (l : loc) (ly : layout) (z : Z) : loc := (l +ₗ ly.(ly_size) * z).
Notation "l 'offset{' ly '}ₗ' z" := (offset_loc l%L ly z%Z)
  (at level 50, format "l  'offset{' ly '}ₗ'  z", left associativity) : loc_scope.
Typeclasses Opaque offset_loc.

Definition aligned_to (l : loc) (n : nat) : Prop := (n | l.2).
Notation "l `aligned_to` n" := (aligned_to l n) (at level 50) : stdpp_scope.
Arguments aligned_to : simpl never.
Typeclasses Opaque aligned_to.

Definition has_layout_loc (l : loc) (ly : layout) : Prop := l `aligned_to` ly_align ly.
Notation "l `has_layout_loc` n" := (has_layout_loc l n) (at level 50) : stdpp_scope.
Arguments has_layout_loc : simpl never.
Typeclasses Opaque has_layout_loc.

Section loc_lemmas.
  (*+ Lemmas about [shift_loc] and [offset_loc] *)
  Lemma shift_loc_assoc l n1 n2 : l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2).
  Proof. rewrite /shift_loc /=. f_equal. lia. Qed.

  Lemma shift_loc_0 l : l +ₗ 0 = l.
  Proof. destruct l as [??]. by rewrite /shift_loc Z.add_0_r. Qed.

  Lemma shift_loc_assoc_nat l (n1 n2 : nat) : l +ₗ n1 +ₗ n2 = l +ₗ (n1 + n2)%nat.
  Proof. rewrite /shift_loc /=. f_equal. lia. Qed.

  Lemma shift_loc_0_nat l : l +ₗ 0%nat = l.
  Proof. have: Z.of_nat 0%nat = 0 by lia. move => ->. apply shift_loc_0. Qed.

  Lemma shift_loc_S l n: l +ₗ S n = (l +ₗ 1%nat +ₗ n).
  Proof. by rewrite shift_loc_assoc_nat. Qed.

  Lemma shift_loc_inj1 l1 l2 n : l1 +ₗ n = l2 +ₗ n → l1 = l2.
  Proof. destruct l1, l2. case => -> ?. f_equal. lia. Qed.

  Global Instance shift_loc_inj2 l : Inj (=) (=) (shift_loc l).
  Proof. destruct l as [b o]; intros n n' [=?]; lia. Qed.

  Lemma shift_loc_block l n : (l +ₗ n).1 = l.1.
  Proof. done. Qed.

  Lemma offset_loc_0 l ly : l offset{ly}ₗ 0 = l.
  Proof. by rewrite /offset_loc Z.mul_0_r shift_loc_0. Qed.

  Lemma offset_loc_S l ly n : l offset{ly}ₗ S n = (l offset{ly}ₗ 1) offset{ly}ₗ n.
  Proof. destruct l. rewrite /offset_loc /shift_loc /=. f_equal. lia. Qed.

  Lemma offset_loc_1 l ly : l offset{ly}ₗ 1%nat = (l +ₗ ly.(ly_size)).
  Proof. destruct l. rewrite /offset_loc /shift_loc /=. f_equal. lia. Qed.

  Lemma offset_loc_sz1 ly l n : ly.(ly_size) = 1%nat → l offset{ly}ₗ n = l +ₗ n.
  Proof. rewrite /offset_loc => ->. f_equal. lia. Qed.

  (*+ Lemmas about [aligned_to] and [has_layout_loc] *)
  Lemma ly_with_align_aligned_to l m n:
    l `aligned_to` n →
    is_power_of_two n →
    l `has_layout_loc` ly_with_align m n.
  Proof. move => ??. by rewrite /has_layout_loc ly_align_ly_with_align keep_factor2_is_power_of_two. Qed.

  Lemma has_layout_loc_trans l ly1 ly2 :
    l `has_layout_loc` ly2 → (ly1.(ly_align_log) ≤ ly2.(ly_align_log))%nat → l `has_layout_loc` ly1.
  Proof. rewrite /has_layout_loc/aligned_to => Hl ?. etrans;[|by apply Hl]. by apply Zdivide_nat_pow. Qed.

  Lemma has_layout_loc_trans' l ly1 ly2 :
    l `has_layout_loc` ly2 → (ly_align ly1 ≤ ly_align ly2)%nat → l `has_layout_loc` ly1.
  Proof. rewrite -ly_align_log_ly_align_le_iff. by apply: has_layout_loc_trans. Qed.

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
    - rewrite/ly_offset. destruct n;[by subst;apply Z.divide_0_r|]. etrans;[apply Zdivide_nat_pow, Min.le_min_r|].   by apply factor2_divide.
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
    unfold aligned_to. destruct l => /=. rewrite Z.add_comm.
    split.
    - apply: Z.divide_add_cancel_r. by apply Z.divide_mul_r.
    - apply Z.divide_add_r. by apply Z.divide_mul_r.
  Qed.

  Lemma aligned_to_mult_eq l n1 n2 off:
    l `aligned_to` n2 → (l +ₗ off) `aligned_to` (n1 * n2) → (n2 | off).
  Proof.
    unfold aligned_to. destruct l => /= ??. apply: Z.divide_add_cancel_r => //.
    apply: (Zdivide_mult_l _ n1). by rewrite Z.mul_comm -Nat2Z.inj_mul.
  Qed.
End loc_lemmas.

(** * Bytes and values stored in memory *)

(** Representation of a byte stored in memory. *)
Inductive mbyte : Set :=
| MByte (b : byte)
| MPtrFrag (l : loc) (n : nat)
| MPoison.

(** Representation of a value (list of bytes). *)
Definition val : Set := list mbyte.
Bind Scope val_scope with val.

Definition has_layout_val (v : val) (ly : layout) : Prop := length v = ly.(ly_size).
Notation "v `has_layout_val` n" := (has_layout_val v n) (at level 50) : stdpp_scope.
Arguments has_layout_val : simpl never.
Typeclasses Opaque has_layout_val.

(** * Representation of the heap *)

Inductive lock_state := WSt | RSt (n : nat).

Record heap_cell := HeapCell {
  hc_alloc_id   : alloc_id;   (** Allocation owning the cell. *)
  hc_lock_state : lock_state; (** Datarace detection stuff. *)
  hc_value      : mbyte;      (** Byte value. *)
}.

Definition heap := gmap addr heap_cell.

(** Predicate stating that the heap [h] contains value [v] at address [a],
and that every cell involved has an allocation identifier and a lock state
that satisfy [Paid] and [Plk] respectively. *)
Fixpoint heap_lookup (a : addr) (v : val) (Paid : alloc_id → Prop)
                       (Plk : lock_state → Prop) (h : heap) : Prop :=
  match v with
  | []     => True
  | b :: v => (∃ aid lk, h !! a = Some (HeapCell aid lk b) ∧ Paid aid ∧ Plk lk) ∧
              heap_lookup (Z.succ a) v Paid Plk h
  end.

(** Function writing value [v] at address [a] in heap [h]. For all involved
cells in the resulting heap, an allocation id and lock state is built using
functions [faid] and [flk] respectively. These functions receive as input
the previous value of the field (if the cell previously existed in [h]). *)
Fixpoint heap_update (a : addr) (v : val) (faid : option alloc_id → alloc_id)
                     (flk : option lock_state → lock_state) (h : heap) : heap :=
  match v with
  | []     => h
  | b :: v => let update m :=
                Some {|
                  hc_alloc_id   := faid (hc_alloc_id <$> m);
                  hc_lock_state := flk (hc_lock_state <$> m);
                  hc_value      := b;
                |}
              in
              partial_alter update a (heap_update (Z.succ a) v faid flk h)
  end.

Definition heap_lookup_loc (l : loc) (v : val) (Plk : lock_state → Prop)
                             (h : heap) : Prop :=
  heap_lookup l.2 v (λ aid, l.1 = Some aid) Plk h.

Definition heap_alloc (a : addr) (v : val) (aid : alloc_id) (h : heap) : heap :=
  heap_update a v (λ _, aid) (λ _, RSt 0%nat) h.

(** Predicate stating that the allocation [aid] is still present in heap [h]. *)
Definition heap_block_alive (h : heap) (aid : alloc_id) : Prop :=
  ∃ a, hc_alloc_id <$> h !! a = Some aid.

Definition heap_at (l : loc) (ly : layout) (v : val) (Plk : lock_state → Prop)
                   (h : heap) : Prop :=
  is_Some l.1 ∧ l `has_layout_loc` ly ∧ v `has_layout_val` ly ∧
  heap_lookup_loc l v Plk h.

Definition heap_upd l v flk h :=
  heap_update l.2 v (λ _, default dummy_alloc_id l.1) flk h.

(** Predicate stating that the [n] first bytes from address [a] in [h] have
not been allocated. *)
Definition heap_range_free (h : heap) (a : addr) (n : nat) : Prop :=
  ∀ a', a ≤ a' < a + n → h !! a' = None.

(** Free [n] cells starting at [a] in [h]. *)
Fixpoint heap_free (a : addr) (n : nat) (h : heap) : heap :=
  match n with
  | O   => h
  | S n => delete a (heap_free (Z.succ a) n h)
  end.

Fixpoint heap_free_list (ls : list (loc * layout)) (h : heap) : heap :=
  match ls with
  | []           => h
  | (l,ly) :: ls => heap_free l.2 ly.(ly_size) (heap_free_list ls h)
  end.

Section heap_lemmas.
  Lemma heap_lookup_inj_val a h v1 v2 Paid1 Paid2 Plk1 Plk2:
    length v1 = length v2 →
    heap_lookup a v1 Paid1 Plk1 h → heap_lookup a v2 Paid2 Plk2 h → v1 = v2.
  Proof.
    elim: v1 v2 a; first by move => [|??] //.
    move => ?? IH [|??] //= ? [?] [[?[?[??]]]?] [[?[?[??]]]?]; simplify_eq.
    f_equal. by apply: IH.
  Qed.

  Lemma heap_update_ext h a v faid1 faid2 flk1 flk2:
    (∀ x, faid1 x = faid2 x) → (∀ x, flk1 x = flk2 x) →
    heap_update a v faid1 flk1 h = heap_update a v faid2 flk2 h.
  Proof.
    move => Hext1 Hext2. elim: v a => //= ?? IH ?. rewrite IH.
    apply: partial_alter_ext => ??. by rewrite Hext1 Hext2.
  Qed.

  Lemma heap_update_lookup_lt a1 a2 v faid flk h:
    a1 < a2 →
    heap_update a2 v faid flk h !! a1 = h !! a1.
  Proof.
    elim: v a1 a2 => // ?? IH ???.
    rewrite lookup_partial_alter_ne; last lia. apply IH. lia.
  Qed.

  Lemma heap_free_delete h a1 a2 n :
    delete a1 (heap_free a2 n h) = heap_free a2 n (delete a1 h).
  Proof. elim: n a2 => //= ? IH ?. by rewrite delete_commute IH. Qed.

  Lemma heap_free_list_app ls1 ls2 h :
    heap_free_list (ls1 ++ ls2) h = heap_free_list ls1 (heap_free_list ls2 h).
  Proof. by elim: ls1 => //= [[??]] ? ->. Qed.

  Lemma heap_upd_ext h l v f1 f2:
    (∀ x, f1 x = f2 x) → heap_upd l v f1 h = heap_upd l v f2 h.
  Proof. by apply heap_update_ext. Qed.

  Lemma heap_at_inj_val l ly h v1 v2 Plk1 Plk2:
    heap_at l ly v1 Plk1 h → heap_at l ly v2 Plk2 h → v1 = v2.
  Proof.
    move => [_[?[??]]] [_[?[??]]].
    apply: heap_lookup_inj_val => //. congruence.
  Qed.

  Lemma heap_lookup_loc_inj_val  l h v v' flk1 flk2 ly:
    v `has_layout_val` ly →
    heap_lookup_loc l v flk1 h → heap_at l ly v' flk2 h → v = v'.
  Proof.
    move => ??[_[?[??]]]. apply: heap_lookup_inj_val => //. congruence.
  Qed.

  Lemma heap_upd_heap_at_id l v flk flk' h:
    heap_lookup_loc l v flk' h →
    (∀ st, flk (Some st) = st) →
    heap_upd l v flk h = h.
  Proof.
    rewrite /heap_upd.
    elim: v l => // ?? IH ? [[?[?[H[H1 ?]]]]?] Hlookup /=.
    assert (∀ l, Z.succ l.2 = (l +ₗ 1).2) as -> by done.
    rewrite IH => //. apply: partial_alter_self_alt'.
    by rewrite H Hlookup H1 /=.
  Qed.
End heap_lemmas.

(** * Allocations and heap state *)

Record allocation :=
  Allocation {
    alloc_start : Z; (* First valid address. *)
    alloc_end : Z;   (* One-past-the-end address. *)
  }.

Definition allocs := gmap alloc_id allocation.

Record heap_state := {
  hs_heap   : heap;
  hs_allocs : allocs;
}.

(** Smallest allocatble address (we reserve 0 for NULL). *)
Definition min_alloc_start : Z := 1.

(** Largest allocatable address (we never allocate the last byte to always
have valid one-past pointers. *)
Definition max_alloc_end : Z := 2 ^ (bytes_per_addr * bits_per_byte) - 2.

Definition to_allocation (off : Z) (len : nat) : allocation :=
  Allocation off (off + len).

Definition allocation_in_range (a : allocation) : Prop :=
  min_alloc_start ≤ a.(alloc_start) ∧ a.(alloc_end) ≤ max_alloc_end.

(** The address range between [l] and [l +ₗ n] (included) is in range of the
    allocation that contains [l]. Note that we consider the 1-past-the-end
    pointer to be in range of an allocation. *)
Definition heap_state_loc_in_bounds (l : loc) (n : nat) (st : heap_state) : Prop :=
  ∃ alloc_id alloc,
    l.1 = Some alloc_id ∧
    st.(hs_allocs) !! alloc_id = Some alloc ∧
    alloc.(alloc_start) ≤ l.2 ∧
    l.2 + n ≤ alloc.(alloc_end).

(** Checks that the location [l] is inbounds of its allocation
(one-past-the-end is allowed) and this allocation is still alive *)
Definition valid_ptr (l : loc) (st : heap_state) : Prop :=
  ∃ aid, l.1 = Some aid ∧ heap_block_alive st.(hs_heap) aid ∧ heap_state_loc_in_bounds l 0 st.

Inductive alloc_new_block : heap_state → loc → val → heap_state → Prop :=
| AllocNewBlock σ l aid v:
    l.1 = Some aid →
    σ.(hs_allocs) !! aid = None →
    (* TODO: is the precondition really useful? It should follow from
    the previous. *)
    ¬ heap_block_alive σ.(hs_heap) aid →
    allocation_in_range (to_allocation l.2 (length v)) →
    heap_range_free σ.(hs_heap) l.2 (length v) →
    alloc_new_block σ l v {|
      hs_heap   := heap_alloc l.2 v aid σ.(hs_heap);
      hs_allocs := <[aid := to_allocation l.2 (length v)]> σ.(hs_allocs);
    |}.

Inductive alloc_new_blocks : heap_state → list loc → list val → heap_state → Prop :=
| AllocNewBlock_nil σ :
    alloc_new_blocks σ [] [] σ
| AllocNewBlock_cons σ σ' σ'' l v ls vs :
    alloc_new_block σ l v σ' →
    alloc_new_blocks σ' ls vs σ'' →
    alloc_new_blocks σ (l :: ls) (v :: vs) σ''.

(** * Definition of the language *)

Definition label := string.
Definition var_name := string.

Inductive op_type : Set :=
| IntOp (i : int_type) | PtrOp.

(* see http://compcert.inria.fr/doc/html/compcert.cfrontend.Cop.html#binary_operation *)
Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | XorOp | ShlOp
| ShrOp | EqOp | NeOp | LtOp | GtOp | LeOp | GeOp
(* Ptr is the second argument and pffset the first *)
| PtrOffsetOp (ly : layout) | PtrNegOffsetOp (ly : layout).

Inductive un_op : Set :=
| NotBoolOp | NotIntOp | NegOp | CastOp (ot : op_type).
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CopyAllocId (e1 : expr) (e2 : expr)
| Deref (o : order) (ly : layout) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| Call (f : expr) (args : list expr)
| Concat (es : list expr)
| IfE (ot : op_type) (e1 e2 e3 : expr)
| SkipE (e : expr)
| StuckE (* stuck expression *)
.
End expr.
Arguments Call _%E _%E.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (e1 e2 : expr), P e1 → P e2 → P (CopyAllocId e1 e2)) →
  (∀ (o : order) (ly : layout) (e : expr), P e → P (Deref o ly e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (f : expr) (args : list expr), P f → Forall P args → P (Call f args)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (IfE ot e1 e2 e3)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall Hconcat *.
  8: { apply Hcall; [ |apply Forall_true => ?]; by apply: FIX. }
  8: { apply Hconcat. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. by move => ?? [->]. Qed.

(** Note that there is no explicit Fork. Instead the initial state can
contain multiple threads (like a processor which has a fixed number of
hardware threads). *)
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
(* m: map from values of e to indices into bs, def: default *)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ly : layout) (e1 e2 : expr) (s : stmt)
| SkipS (s : stmt)
| StuckS (* stuck statement *)
| ExprS (e : expr) (s : stmt)
.

Arguments Switch _%E _%E _%E.

Record function := {
  f_args : list (var_name * layout);
  f_local_vars : list (var_name * layout);
  (* TODO should we add this: f_ret : layout; ?*)
  f_code : gmap label stmt;
  f_init : label;
}.

(* TODO: put both function and bytes in the same heap or make pointers disjoint *)
Record state := {
  st_heap: heap_state;
  st_fntbl: gmap loc function;
}.

Definition heap_fmap (f : heap → heap) (σ : state) := {|
  st_heap := {| hs_heap := f σ.(st_heap).(hs_heap); hs_allocs := σ.(st_heap).(hs_allocs) |};
  st_fntbl := σ.(st_fntbl);
|}.

Record runtime_function := {
  (* locations of args and local vars are substitued in the body *)
  rf_fn : function;
  (* locations in the stack frame (locations of arguments and local
  vars allocated on Call, need to be freed by Return) *)
  rf_locs: list (loc * layout);
}.

Inductive runtime_expr :=
| Expr (e : rtexpr)
| Stmt (rf : runtime_function) (s : rtstmt)
| AllocFailed
with rtexpr :=
| RTVar (x : var_name)
| RTVal (v : val)
| RTUnOp (op : un_op) (ot : op_type) (e : runtime_expr)
| RTBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : runtime_expr)
| RTCopyAllocId (e1 : runtime_expr) (e2 : runtime_expr)
| RTDeref (o : order) (ly : layout) (e : runtime_expr)
| RTCall (f : runtime_expr) (args : list runtime_expr)
| RTCAS (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTConcat (es : list runtime_expr)
| RTIfE (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTSkipE (e : runtime_expr)
| RTStuckE
with rtstmt :=
| RTGoto (b : label)
| RTReturn (e : runtime_expr)
| RTSwitch (it : int_type) (e : runtime_expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| RTAssign (o : order) (ly : layout) (e1 e2 : runtime_expr) (s : stmt)
| RTSkipS (s : stmt)
| RTStuckS
| RTExprS (e : runtime_expr) (s : stmt)
.

Fixpoint to_rtexpr (e : expr) : runtime_expr :=
  Expr $ match e with
  | Var x => RTVar x
  | Val v => RTVal v
  | UnOp op ot e => RTUnOp op ot (to_rtexpr e)
  | BinOp op ot1 ot2 e1 e2 => RTBinOp op ot1 ot2 (to_rtexpr e1) (to_rtexpr e2)
  | CopyAllocId e1 e2 => RTCopyAllocId (to_rtexpr e1) (to_rtexpr e2)
  | Deref o ly e => RTDeref o ly (to_rtexpr e)
  | Call f args => RTCall (to_rtexpr f) (to_rtexpr <$> args)
  | CAS ot e1 e2 e3 => RTCAS ot (to_rtexpr e1) (to_rtexpr e2) (to_rtexpr e3)
  | Concat es => RTConcat (to_rtexpr <$> es)
  | IfE ot e1 e2 e3 => RTIfE ot (to_rtexpr e1) (to_rtexpr e2) (to_rtexpr e3)
  | SkipE e => RTSkipE (to_rtexpr e)
  | StuckE => RTStuckE
  end.
Definition coerce_rtexpr := to_rtexpr.
Coercion coerce_rtexpr : expr >-> runtime_expr.
Arguments coerce_rtexpr : simpl never.
Definition to_rtstmt (rf : runtime_function) (s : stmt) : runtime_expr :=
  Stmt rf $ match s with
  | Goto b => RTGoto b
  | Return e => RTReturn (to_rtexpr e)
  | Switch it e m bs def => RTSwitch it (to_rtexpr e) m bs def
  | Assign o ly e1 e2 s => RTAssign o ly (to_rtexpr e1) (to_rtexpr e2) s
  | SkipS s => RTSkipS s
  | StuckS => RTStuckS
  | ExprS e s => RTExprS (to_rtexpr e) s
  end.

Global Instance to_rtexpr_inj : Inj (=) (=) to_rtexpr.
Proof.
  elim => [ ^ e1 ] [ ^ e2 ] // ?; simplify_eq => //; try naive_solver.
  - f_equal. naive_solver.
    generalize dependent e2args.
    revert select (Forall _ _). elim. by case.
    move => ????? [|??]//. naive_solver.
  - generalize dependent e2es.
    revert select (Forall _ _). elim. by case.
    move => ????? [|??]//. naive_solver.
Qed.
Global Instance to_rtstmt_inj : Inj2 (=) (=) (=) to_rtstmt.
Proof. move => ? s1 ? s2 [-> ]. elim: s1 s2 => [ ^ e1 ] [ ^ e2 ] // ?; simplify_eq => //. Qed.

Implicit Type (l : loc) (re : rtexpr) (v : val) (sz : nat) (h : heap) (σ : state) (ly : layout) (rs : rtstmt) (s : stmt) (sgn : signed) (rf : runtime_function).

(*** Relating val to logical values *)
(*+ [val_to_int] and [val_of_int] *)
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

(*+ [val_to_loc] and [val_of_loc] *)
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

(*+ [val_of_bool] and [i2v] *)
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
Arguments val_to_loc : simpl never.
Arguments val_of_loc : simpl never.
Typeclasses Opaque val_to_loc val_of_loc val_to_int val_of_int val_of_bool.

(*** Substitution *)
Fixpoint subst (x : var_name) (v : val) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | UnOp op ot e => UnOp op ot (subst x v e)
  | BinOp op ot1 ot2 e1 e2 => BinOp op ot1 ot2 (subst x v e1) (subst x v e2)
  | CopyAllocId e1 e2 => CopyAllocId (subst x v e1) (subst x v e2)
  | Deref o l e => Deref o l (subst x v e)
  | Call e es => Call (subst x v e) (subst x v <$> es)
  | CAS ly e1 e2 e3 => CAS ly (subst x v e1) (subst x v e2) (subst x v e3)
  | Concat el => Concat (subst x v <$> el)
  | IfE ot e1 e2 e3 => IfE ot (subst x v e1) (subst x v e2) (subst x v e3)
  | SkipE e => SkipE (subst x v e)
  | StuckE => StuckE
  end.

Fixpoint subst_l (xs : list (var_name * val)) (e : expr)  : expr :=
  match xs with
  | (x, v)::xs' => subst_l xs' (subst x v e)
  | _ => e
  end.

Fixpoint subst_stmt (xs : list (var_name * val)) (s : stmt) : stmt :=
  match s with
  | Goto b => Goto b
  | Return e => Return (subst_l xs e)
  | Switch it e m' bs def => Switch it (subst_l xs e) m' (subst_stmt xs <$> bs) (subst_stmt xs def)
  | Assign o ly e1 e2 s => Assign o ly (subst_l xs e1) (subst_l xs e2) (subst_stmt xs s)
  | SkipS s => SkipS (subst_stmt xs s)
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_l xs e) (subst_stmt xs s)
  end.

Definition subst_function (xs : list (var_name * val)) (f : function) : function := {|
  f_code := (subst_stmt xs) <$> f.(f_code);
  f_args := f.(f_args); f_init := f.(f_init); f_local_vars := f.(f_local_vars);
|}.

(*** Evaluation of operations *)

(* evaluation can be non-deterministic for comparing pointers *)
Inductive eval_bin_op : bin_op → op_type → op_type → state → val → val → val → Prop :=
| PtrOffsetOpIP v1 v2 σ o l ly it:
    val_to_int v1 it = Some o →
    val_to_loc v2 = Some l →
    (* TODO: should we have an alignment check here? *)
    0 ≤ o →
    eval_bin_op (PtrOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ o))
| PtrNegOffsetOpIP v1 v2 σ o l ly it:
    val_to_int v1 it = Some o →
    val_to_loc v2 = Some l →
    (* TODO: should we have an alignment check here? *)
    eval_bin_op (PtrNegOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ -o))
| EqOpPNull v1 v2 σ l v:
    heap_state_loc_in_bounds l 0%nat σ.(st_heap) →
    val_to_loc v1 = Some l →
    val_to_int v2 size_t = Some 0 →
    (* TODO ( see below ): Should we really hard code i32 here because of C? *)
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp σ v1 v2 v
| NeOpPNull v1 v2 σ l v:
    heap_state_loc_in_bounds l 0%nat σ.(st_heap) →
    val_to_loc v1 = Some l →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp σ v1 v2 v
| EqOpNullNull v1 v2 σ v:
    val_to_int v1 size_t = Some 0 →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp σ v1 v2 v
| NeOpNullNull v1 v2 σ v:
    val_to_int v1 size_t = Some 0 →
    val_to_int v2 size_t = Some 0 →
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp σ v1 v2 v
| RelOpPP v1 v2 σ l1 l2 v b op:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    valid_ptr l1 σ.(st_heap) → valid_ptr l2 σ.(st_heap) →
    match op with
    | EqOp => Some (bool_decide (l1.2 = l2.2))
    | NeOp => Some (bool_decide (l1.2 ≠ l2.2))
    | LtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 < l2.2)) else None
    | GtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 > l2.2)) else None
    | LeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 <= l2.2)) else None
    | GeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 >= l2.2)) else None
    | _ => None
    end = Some b →
    i2v (Z_of_bool b) i32 = v →
    eval_bin_op op PtrOp PtrOp σ v1 v2 v
| RelOpII op v1 v2 σ n1 n2 it b:
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
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 (i2v (Z_of_bool b) i32)
| ArithOpII op v1 v2 σ n1 n2 it n v:
    match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    (* we need to take `quot` and `rem` here for the correct rounding
    behavior, i.e. rounding towards 0 (instead of `div` and `mod`,
    which round towards floor)*)
    | DivOp => if bool_decide (n2 ≠ 0) then Some (n1 `quot` n2) else None
    | ModOp => if bool_decide (n2 ≠ 0) then Some (n1 `rem` n2) else None
    | AndOp => Some (Z.land n1 n2)
    | OrOp => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    (* For shift operators (`ShlOp` and `ShrOp`), behaviors are defined if:
       - lhs is nonnegative, and
       - rhs (also nonnegative) is less than the number of bits in lhs.
       See: https://en.cppreference.com/w/c/language/operator_arithmetic, "Shift operators". *)
    | ShlOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≪ n2) else None
    (* NOTE: when lhs is negative, Coq's `≫` is not semantically equivalent to C's `>>`.
       Counterexample: Coq `-1000 ≫ 10 = 0`; C `-1000 >> 10 == -1`.
       This is because `≫` is implemented by `Z.div`. *)
    | ShrOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≫ n2) else None
    | _ => None
    end = Some n →
    val_to_int v1 it = Some n1 →
    val_to_int v2 it = Some n2 →
    val_of_int (if it_signed it then n else n `mod` int_modulus it) it = Some v →
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 v
.

Inductive eval_un_op : un_op → op_type → state → val → val → Prop :=
| CastOpII itt its σ vs vt n:
    val_to_int vs its = Some n →
    val_of_int n itt = Some vt →
    eval_un_op (CastOp (IntOp itt)) (IntOp its) σ vs vt
| CastOpPP σ vs vt l:
    val_to_loc vs = Some l →
    val_of_loc l = vt →
    eval_un_op (CastOp PtrOp) PtrOp σ vs vt
| CastOpPI it σ vs vt l:
    val_to_loc vs = Some l →
    val_of_int l.2 it = Some vt →
    eval_un_op (CastOp (IntOp it)) PtrOp σ vs vt
| CastOpIP it σ vs vt n:
    val_to_int vs it = Some n →
    val_of_loc (None, n) = vt →
    eval_un_op (CastOp PtrOp) (IntOp it) σ vs vt
| NegOpI it σ vs vt n:
    val_to_int vs it = Some n →
    val_of_int (-n) it = Some vt →
    eval_un_op NegOp (IntOp it) σ vs vt
.

(*** Evaluation of Expressions *)

Inductive expr_step : expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| SkipES v σ:
    expr_step (SkipE (Val v)) σ [] (Val v) σ []
| UnOpS op v σ v' ot:
    eval_un_op op ot σ v v' →
    expr_step (UnOp op ot (Val v)) σ [] (Val v') σ []
| BinOpS op v1 v2 σ v' ot1 ot2:
    eval_bin_op op ot1 ot2 σ v1 v2 v' →
    expr_step (BinOp op ot1 ot2 (Val v1) (Val v2)) σ [] (Val v') σ []
| DerefS o v l ly v' σ:
    let start_st st := ∃ n, st = if o is Na2Ord then RSt (S n) else RSt n in
    let end_st st :=
      match o, st with
      | Na1Ord, Some (RSt n)     => RSt (S n)
      | Na2Ord, Some (RSt (S n)) => RSt n
      | ScOrd , Some st          => st
      |  _    , _                => WSt (* unreachable *)
      end
    in
    let end_expr := if o is Na1Ord then Deref Na2Ord ly (Val v) else Val v' in
    val_to_loc v = Some l →
    heap_at l ly v' start_st σ.(st_heap).(hs_heap) →
    expr_step (Deref o ly (Val v)) σ [] end_expr (heap_fmap (heap_upd l v' end_st) σ) []
(* TODO: look at CAS and see whether it makes sense. Also allow
comparing pointers? (see lambda rust) *)
(* corresponds to atomic_compare_exchange_strong, see https://en.cppreference.com/w/c/atomic/atomic_compare_exchange *)
| CasFailS l1 l2 vo ve σ z1 z2 v1 v2 v3 it:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_int vo it = Some z1 →
    val_to_int ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool false)) (heap_fmap (heap_upd l2 vo (λ _, RSt 0%nat)) σ) []
| CasSucS l1 l2 it vo ve σ z1 z2 v1 v2 v3:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_int vo it = Some z1 →
    val_to_int ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 = z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool true)) (heap_fmap (heap_upd l1 v3 (λ _, RSt 0%nat)) σ) []
| CallS lsa lsv σ σ' σ'' vf vs f rf fn fn' :
    val_to_loc vf = Some f →
    σ.(st_fntbl) !! f = Some fn →
    length lsa = length fn.(f_args) →
    length lsv = length fn.(f_local_vars) →
    (* substitute the variables in fn with the corresponding locations *)
    fn' = subst_function (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1) (val_of_loc <$> (lsa ++ lsv))) fn →
    (* check the layout of the arguments *)
    Forall2 has_layout_val vs fn.(f_args).*2 →
    (* ensure that locations are aligned *)
    Forall2 has_layout_loc lsa fn.(f_args).*2 →
    Forall2 has_layout_loc lsv fn.(f_local_vars).*2 →
    (* initialize the local vars to poison *)
    alloc_new_blocks σ.(st_heap) lsv ((λ p, replicate p.2.(ly_size) MPoison) <$> fn.(f_local_vars)) σ'.(st_heap) →
    σ.(st_fntbl) = σ'.(st_fntbl) →
    (* initialize the arguments with the supplied values *)
    alloc_new_blocks σ'.(st_heap) lsa vs σ''.(st_heap) →
    σ'.(st_fntbl) = σ''.(st_fntbl) →
    (* add used blocks allocations  *)
    rf = {| rf_fn := fn'; rf_locs := zip lsa fn.(f_args).*2 ++ zip lsv fn.(f_local_vars).*2; |} →
    expr_step (Call (Val vf) (Val <$> vs)) σ [] (to_rtstmt rf (Goto fn'.(f_init))) σ'' []
| CallFailS σ vf vs f fn:
    val_to_loc vf = Some f →
    σ.(st_fntbl) !! f = Some fn →
    Forall2 has_layout_val vs fn.(f_args).*2 →
    expr_step (Call (Val vf) (Val <$> vs)) σ [] AllocFailed σ []
| ConcatS vs σ:
    expr_step (Concat (Val <$> vs)) σ [] (Val (mjoin vs)) σ []
| CopyAllocIdS l1 l2 v1 v2 σ:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    expr_step (CopyAllocId (Val v1) (Val v2)) σ [] (Val (val_of_loc (l2.1, l1.2))) σ []
| IfES v it e1 e2 n σ:
    val_to_int v it = Some n →
    expr_step (IfE (IntOp it) (Val v) e1 e2) σ [] (if bool_decide (n ≠ 0) then e1 else e2)  σ []
(* no rule for StuckE *)
.

(*** Evaluation of statements *)
Inductive stmt_step : stmt → runtime_function → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| AssignS (o : order) rf σ s v1 v2 l v' ly:
    let start_st st := st = if o is Na2Ord then WSt else RSt 0%nat in
    let end_st _ := if o is Na1Ord then WSt else RSt 0%nat in
    let end_val  := if o is Na1Ord then v' else v2 in
    let end_stmt := if o is Na1Ord then Assign Na2Ord ly (Val v1) (Val v2) s else s in
    val_to_loc v1 = Some l →
    v2 `has_layout_val` ly →
    heap_at l ly v' start_st σ.(st_heap).(hs_heap) →
    stmt_step (Assign o ly (Val v1) (Val v2) s) rf σ [] (to_rtstmt rf end_stmt) (heap_fmap (heap_upd l end_val end_st) σ) []
| SwitchS rf σ v n m bs s def it :
    val_to_int v it = Some n →
    (∀ i : nat, m !! n = Some i → is_Some (bs !! i)) →
    stmt_step (Switch it (Val v) m bs def) rf σ [] (to_rtstmt rf (default def (i ← m !! n; bs !! i))) σ []
| GotoS rf σ b s :
    rf.(rf_fn).(f_code) !! b = Some s →
    stmt_step (Goto b) rf σ [] (to_rtstmt rf s) σ []
| ReturnS rf σ v:
    stmt_step (Return (Val v)) rf σ [] (Val v)
     (* deallocate the stack *)
     (heap_fmap (heap_free_list rf.(rf_locs)) σ) []
| SkipSS rf σ s :
    stmt_step (SkipS s) rf σ [] (to_rtstmt rf s) σ []
| ExprSS rf σ s v:
    stmt_step (ExprS (Val v) s) rf σ [] (to_rtstmt rf s) σ []
(* no rule for StuckS *)
.

(*** Evaluation of runtime_expr *)
Inductive runtime_step : runtime_expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| ExprStep e σ κs e' σ' efs:
    expr_step e σ κs e' σ' efs →
    runtime_step (to_rtexpr e) σ κs e' σ' efs
| StmtStep s rf σ κs e' σ' efs:
    stmt_step s rf σ κs e' σ' efs →
    runtime_step (to_rtstmt rf s) σ κs e' σ' efs
| AllocFailedStep σ :
    (* Alloc failure is nb, not ub so we go into an infinite loop*)
    runtime_step AllocFailed σ [] AllocFailed σ [].

(*** evaluation contexts *)
(** for expressions*)
Inductive expr_ectx :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : runtime_expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CopyAllocIdLCtx (e2 : runtime_expr)
| CopyAllocIdRCtx (v1 : val)
| DerefCtx (o : order) (l : layout)
| CallLCtx (args : list runtime_expr)
| CallRCtx (f : val) (vl : list val) (el : list runtime_expr)
| CASLCtx (ot : op_type) (e2 e3 : runtime_expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : runtime_expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| ConcatCtx (vs : list val) (es : list runtime_expr)
| IfECtx (ot : op_type) (e2 e3 : runtime_expr)
| SkipECtx
.

Definition expr_fill_item (Ki : expr_ectx) (e : runtime_expr) : rtexpr :=
  match Ki with
  | UnOpCtx op ot => RTUnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => RTBinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => RTBinOp op ot1 ot2 (Val v1) e
  | CopyAllocIdLCtx e2 => RTCopyAllocId e e2
  | CopyAllocIdRCtx v1 => RTCopyAllocId (Val v1) e
  | DerefCtx o l => RTDeref o l e
  | CallLCtx args => RTCall e args
  | CallRCtx f vl el => RTCall (Val f) ((Expr <$> (RTVal <$> vl)) ++ e :: el)
  | CASLCtx ot e2 e3 => RTCAS ot e e2 e3
  | CASMCtx ot v1 e3 => RTCAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => RTCAS ot (Val v1) (Val v2) e
  | ConcatCtx vs es => RTConcat ((Expr <$> (RTVal <$> vs)) ++ e :: es)
  | IfECtx ot e2 e3 => RTIfE ot e e2 e3
  | SkipECtx => RTSkipE e
  end.

(** Statements *)
Inductive stmt_ectx :=
(* Assignment is evalutated right to left, otherwise we need to split contexts *)
| AssignRCtx (o : order) (ly : layout) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ly : layout) (v2 : val) (s : stmt)
| ReturnCtx
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| ExprSCtx (s : stmt)
.

Definition stmt_fill_item (Ki : stmt_ectx) (e : runtime_expr) : rtstmt :=
  match Ki with
  | AssignRCtx o ly e1 s => RTAssign o ly e1 e s
  | AssignLCtx o ly v2 s => RTAssign o ly e (Val v2) s
  | ReturnCtx => RTReturn e
  | SwitchCtx it m bs def => RTSwitch it e m bs def
  | ExprSCtx s => RTExprS e s
  end.
Definition to_val (e : runtime_expr) : option val :=
  match e with
  | Expr (RTVal v) => Some v
  | _ => None
  end.

Definition of_val (v : val) : runtime_expr := Expr (RTVal v).

Inductive lang_ectx :=
| ExprCtx (E : expr_ectx)
| StmtCtx (E : stmt_ectx) (rf : runtime_function).

Definition lang_fill_item (Ki : lang_ectx) (e : runtime_expr) : runtime_expr :=
  match Ki with
  | ExprCtx E => Expr (expr_fill_item E e)
  | StmtCtx E rf => Stmt rf (stmt_fill_item E e)
  end.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Expr <$> (RTVal <$> vl1)) ++ e1 :: el1 = (Expr <$> (RTVal <$> vl2)) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_eq_false vl1 vl2 e el :
  to_val e = None → to_rtexpr <$> (Val <$> vl1) = (Expr <$> (RTVal <$> vl2)) ++ e :: el → False.
Proof.
  move => He. elim: vl2 vl1 => [[]//=*|v vl2 IH [|??]?]; csimpl in *; simplify_eq; eauto.
Qed.

Lemma of_to_val (e : runtime_expr) v : to_val e = Some v → Expr (RTVal v) = e.
Proof. case: e => // -[]//. naive_solver. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  runtime_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1 => //. revert select (expr_step _ _ _ _ _ _). by destruct 1. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (lang_fill_item Ki).
Proof. destruct Ki as [E|E ?]; destruct E; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (lang_fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki as [[]|[] ?]; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  lang_fill_item Ki1 e1 = lang_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move: Ki1 Ki2 => [ ^ Ki1] [ ^Ki2] He1 He2 ? //; simplify_eq; try done; f_equal.
  all: destruct Ki1E, Ki2E => //; simplify_eq => //.
  all: efeed pose proof list_expr_val_eq_inv as HEQ; [| | done |] => //; naive_solver.
Qed.

Lemma expr_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  runtime_step (lang_fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki as [[]|[]?]; inversion 1; simplify_eq.
  all: try (revert select (expr_step _ _ _ _ _ _)).
  all: try (revert select (stmt_step _ _ _ _ _ _ _)).
  all: inversion 1; simplify_eq/=; eauto.
  all: apply not_eq_None_Some; intros ?; by eapply list_expr_val_eq_false.
Qed.

Lemma c_lang_mixin : EctxiLanguageMixin of_val to_val lang_fill_item runtime_step.
Proof.
  split => //; eauto using of_to_val, val_stuck, fill_item_inj, fill_item_val, fill_item_no_val_inj, expr_ctx_step_val.
Qed.
Canonical Structure c_ectxi_lang := EctxiLanguage c_lang_mixin.
Canonical Structure c_ectx_lang := EctxLanguageOfEctxi c_ectxi_lang.
Canonical Structure c_lang := LanguageOfEctx c_ectx_lang.

(** * Useful instances and canonical structures *)

Instance mbyte_inhabited : Inhabited mbyte := populate (MPoison).
Instance val_inhabited : Inhabited val := _.
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance stmt_inhabited : Inhabited stmt := populate (Goto "a").
Instance function_inhabited : Inhabited function :=
  populate {| f_args := []; f_local_vars := []; f_code := ∅; f_init := "" |}.
Instance heap_state_inhabited : Inhabited heap_state :=
  populate {| hs_heap := inhabitant; hs_allocs := inhabitant; |}.
Instance state_inhabited : Inhabited state :=
  populate {| st_heap := inhabitant; st_fntbl := inhabitant; |}.

Canonical Structure mbyteO := leibnizO mbyte.
Canonical Structure functionO := leibnizO function.
Canonical Structure locO := leibnizO loc.
Canonical Structure alloc_idO := leibnizO alloc_id.
Canonical Structure layoutO := leibnizO layout.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.
Canonical Structure allocationO := leibnizO allocation.
