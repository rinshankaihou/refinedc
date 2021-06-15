From stdpp Require Import gmap list.
From refinedc.lang Require Export base byte layout int_type loc val.
Set Default Proof Using "Type".
Open Scope Z_scope.

(** * Heap and allocations. *)

(** ** Representation of the heap. *)

Inductive lock_state := WSt | RSt (n : nat).

Record heap_cell := HeapCell {
  hc_alloc_id   : alloc_id;   (** Allocation owning the cell. *)
  hc_lock_state : lock_state; (** Datarace detection stuff. *)
  hc_value      : mbyte;      (** Byte value. *)
}.

Definition heap := gmap addr heap_cell.

(** ** Functions and predicates for manipulating the heap. *)

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
  heap_lookup l.2 v (λ aid, l.1 = ProvAlloc (Some aid)) Plk h.

Definition heap_alloc (a : addr) (v : val) (aid : alloc_id) (h : heap) : heap :=
  heap_update a v (λ _, aid) (λ _, RSt 0%nat) h.

Definition heap_at (l : loc) (ly : layout) (v : val) (Plk : lock_state → Prop)
                   (h : heap) : Prop :=
  (∃ aid, l.1 = ProvAlloc (Some aid))  ∧ l `has_layout_loc` ly ∧ v `has_layout_val` ly ∧
  heap_lookup_loc l v Plk h.

Definition heap_upd (l : loc) v flk h :=
  heap_update l.2 v (default (default dummy_alloc_id (prov_alloc_id l.1))) flk h.

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

(** ** Lemmas about the heap and related operations. *)

Lemma heap_lookup_inj_val a h v1 v2 Paid1 Paid2 Plk1 Plk2:
  length v1 = length v2 →
  heap_lookup a v1 Paid1 Plk1 h → heap_lookup a v2 Paid2 Plk2 h → v1 = v2.
Proof.
  elim: v1 v2 a; first by move => [|??] //.
  move => ?? IH [|??] //= ? [?] [[?[?[??]]]?] [[?[?[??]]]?]; simplify_eq.
  f_equal. by apply: IH.
Qed.

Lemma heap_lookup_is_Some a p v Paid Plk h:
  heap_lookup a v Paid Plk h →
  a ≤ p < a + length v →
  is_Some (h !! p).
Proof.
  elim: v a => /=; first lia. move => b v IH a [[aid [lk [Ha _]]] H] Hp.
  destruct (decide (p = a)) as [->|]; first naive_solver.
  apply (IH (Z.succ a)) => //. lia.
Qed.

Lemma heap_update_ext h a v faid1 faid2 flk1 flk2:
  (∀ x, faid1 x = faid2 x) → (∀ x, flk1 x = flk2 x) →
  heap_update a v faid1 flk1 h = heap_update a v faid2 flk2 h.
Proof.
  move => Hext1 Hext2. elim: v a => //= ?? IH ?. rewrite IH.
  apply: partial_alter_ext => ??. by rewrite Hext1 Hext2.
Qed.

Lemma heap_update_lookup_not_in_range a1 a2 v faid flk h:
  a1 < a2 ∨ a2 + length v ≤ a1 →
  heap_update a2 v faid flk h !! a1 = h !! a1.
Proof.
  elim: v a1 a2 => // ?? IH ?? H.
  rewrite lookup_partial_alter_ne /=; first apply IH; move: H => [] /=; lia.
Qed.

Lemma heap_update_lookup_in_range a1 a2 v faid flk h:
  a2 ≤ a1 < a2 + length v →
  heap_update a2 v faid flk h !! a1 = Some {|
    hc_alloc_id := faid (hc_alloc_id <$> h !! a1);
    hc_lock_state := flk (hc_lock_state <$> h !! a1);
    hc_value := default MPoison (v !! (Z.to_nat (a1 - a2)));
  |}.
Proof.
  elim: v a1 a2.
  - move => /= a1 a2 [??]. exfalso. lia.
  - move => ?? IH a1 a2 [H1 H2]. destruct (decide (a1 = a2)) as [->|Hne].
    + rewrite lookup_partial_alter -/heap_update Z.sub_diag /=.
      rewrite heap_update_lookup_not_in_range; [done | lia].
    + rewrite lookup_partial_alter_ne // -/heap_update /= IH; last first.
      { rewrite /= in H2. lia. } do 3 f_equal.
      rewrite lookup_cons_ne_0; last lia. f_equal. lia.
Qed.

Lemma heap_free_delete h a1 a2 n :
  delete a1 (heap_free a2 n h) = heap_free a2 n (delete a1 h).
Proof. elim: n a2 => //= ? IH ?. by rewrite delete_commute IH. Qed.

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

Lemma heap_free_lookup_in_range a p (n : nat) h:
  a ≤ p < a + n →
  heap_free a n h !! p = None.
Proof.
  elim: n a; first lia. move => n IH a [H1 H2] /=.
  rewrite lookup_delete_None.
  destruct (decide (a = p)) as [->|]; [by left|right].
  apply: IH. lia.
Qed.

Lemma heap_free_lookup_not_in_range a p (n : nat) h:
  ¬ (a ≤ p < a + n) →
  heap_free a n h !! p = h !! p.
Proof.
  elim: n a => //= n IH a H.
  destruct (decide (a = p)) as [->|]; first lia.
  rewrite lookup_delete_ne; last done. apply IH. lia.
Qed.

(** ** Representation of allocations. *)

Record allocation :=
  Allocation {
    al_start : Z;    (* First valid address. *)
    al_len   : nat;  (* Number of allocated byte. *)
    al_alive : bool; (* Is the allocation still alive. *)
  }.

Definition al_end (al : allocation) : Z :=
  al_start al + al_len al.

Definition allocs := gmap alloc_id allocation.

Definition alloc_same_range (al1 al2 : allocation) : Prop :=
  al1.(al_start) = al2.(al_start) ∧ al1.(al_len) = al2.(al_len).

Definition killed (al : allocation) : allocation :=
  {| al_start := al.(al_start); al_len := al.(al_len); al_alive := false; |}.

(** Smallest allocatable address (we reserve 0 for NULL). *)
Definition min_alloc_start : Z := 1.

(** Largest allocatable address (we never allocate the last byte to always
have valid one-past pointers. *)
Definition max_alloc_end : Z := 2 ^ (bytes_per_addr * bits_per_byte) - 2.

(** Predicate asserting that allocation [a] is in range of the allocatable
memory (e.g., does not contain NULL). *)
Definition allocation_in_range (al : allocation) : Prop :=
  min_alloc_start ≤ al.(al_start) ∧ al_end al ≤ max_alloc_end.

Instance elem_of_alloc : ElemOf addr allocation :=
  λ a al, al.(al_start) ≤ a < al_end al.

(** ** Representation of the state of the heap and allocation operations. *)

Record heap_state := {
  hs_heap   : heap;
  hs_allocs : allocs;
}.

Definition alloc_id_alive (aid : alloc_id) (st : heap_state) : Prop :=
  ∃ alloc, st.(hs_allocs) !! aid = Some alloc ∧ alloc.(al_alive).

Definition block_alive (l : loc) (st : heap_state) : Prop :=
  ∃ aid, l.1 = ProvAlloc (Some aid) ∧ alloc_id_alive aid st.

(** The address range between [l] and [l +ₗ n] (included) is in range of the
    allocation that contains [l]. Note that we consider the 1-past-the-end
    pointer to be in range of an allocation. *)
Definition heap_state_loc_in_bounds (l : loc) (n : nat) (st : heap_state) : Prop :=
  ∃ alloc_id al,
    l.1 = ProvAlloc (Some alloc_id) ∧
    st.(hs_allocs) !! alloc_id = Some al ∧
    al.(al_start) ≤ l.2 ∧
    l.2 + n ≤ al_end al.

(** Checks that the location [l] is inbounds of its allocation
(one-past-the-end is allowed) and this allocation is still alive *)
Definition valid_ptr (l : loc) (st : heap_state) : Prop :=
  block_alive l st ∧ heap_state_loc_in_bounds l 0 st.

Definition addr_in_range_alloc (a : addr) (aid : alloc_id) (st : heap_state) : Prop :=
  ∃ alloc, st.(hs_allocs) !! aid = Some alloc ∧ a ∈ alloc.

Inductive alloc_new_block : heap_state → loc → val → heap_state → Prop :=
| AllocNewBlock σ l aid v:
    let alloc := Allocation l.2 (length v) true in
    l.1 = ProvAlloc (Some aid) →
    σ.(hs_allocs) !! aid = None →
    allocation_in_range alloc →
    heap_range_free σ.(hs_heap) l.2 (length v) →
    alloc_new_block σ l v {|
      hs_heap   := heap_alloc l.2 v aid σ.(hs_heap);
      hs_allocs := <[aid := alloc]> σ.(hs_allocs);
    |}.

Inductive alloc_new_blocks : heap_state → list loc → list val → heap_state → Prop :=
| AllocNewBlock_nil σ :
    alloc_new_blocks σ [] [] σ
| AllocNewBlock_cons σ σ' σ'' l v ls vs :
    alloc_new_block σ l v σ' →
    alloc_new_blocks σ' ls vs σ'' →
    alloc_new_blocks σ (l :: ls) (v :: vs) σ''.

Inductive free_block : heap_state → loc → layout → heap_state → Prop :=
| FreeBlock σ l aid ly v:
    let al_alive := Allocation l.2 ly.(ly_size) true  in
    let al_dead  := Allocation l.2 ly.(ly_size) false in
    l.1 = ProvAlloc (Some aid) →
    σ.(hs_allocs) !! aid = Some al_alive →
    length v = ly.(ly_size) →
    heap_lookup_loc l v (λ st, st = RSt 0%nat) σ.(hs_heap) →
    free_block σ l ly {|
      hs_heap   := heap_free l.2 ly.(ly_size) σ.(hs_heap);
      hs_allocs := <[aid := al_dead]> σ.(hs_allocs);
    |}.

Inductive free_blocks : heap_state → list (loc * layout) → heap_state → Prop :=
| FreeBlocks_nil σ :
    free_blocks σ [] σ
| FreeBlocks_cons σ σ' σ'' l ly ls :
    free_block σ l ly σ' →
    free_blocks σ' ls σ'' →
    free_blocks σ ((l, ly) :: ls) σ''.

Lemma heap_state_loc_in_bounds_has_alloc_id l n σ:
  heap_state_loc_in_bounds l n σ → ∃ aid, l.1 = ProvAlloc (Some aid).
Proof. rewrite /heap_state_loc_in_bounds. naive_solver. Qed.

Lemma valid_ptr_has_alloc_id l σ:
  valid_ptr l σ → ∃ aid, l.1 = ProvAlloc (Some aid).
Proof. rewrite /valid_ptr => ?. apply: heap_state_loc_in_bounds_has_alloc_id. naive_solver. Qed.

Lemma free_block_inj hs l ly hs1 hs2:
  free_block hs l ly hs1 → free_block hs l ly hs2 → hs1 = hs2.
Proof. destruct l. inversion 1; simplify_eq. by inversion 1; simplify_eq/=. Qed.

Lemma free_blocks_inj hs1 hs2 hs ls:
  free_blocks hs ls hs1 → free_blocks hs ls hs2 → hs1 = hs2.
Proof.
  move Heq: {1}(hs) => hs' Hb.
  elim: Hb hs Heq. { move => ?? ->. by inversion 1. }
  move => ?????? Hb1 ? IH ??.
  inversion 1; simplify_eq. apply: IH; [|done].
  by apply: free_block_inj.
Qed.

(** ** Heap state invariant definition. *)

(** Predicate stating that every address [a] mapped by the heap of [st] has
a corresponding allocation that encompasses [a] itself. *)
Definition heap_state_heap_cell_in_range_alloc (st : heap_state) :=
  ∀ a hc,
    st.(hs_heap) !! a = Some hc →
    addr_in_range_alloc a hc.(hc_alloc_id) st.

(** Predicate stating that every address [a] mapped by the heap of [st] has
a corresponding alive allocation. *)
Definition heap_state_heap_cell_alloc_alive (st : heap_state) :=
  ∀ a hc,
    st.(hs_heap) !! a = Some hc →
    alloc_id_alive hc.(hc_alloc_id) st.

(** Predicate stating that all allocations in [st] are in range of memory
that can be allocated. *)
Definition heap_state_alloc_in_range (st : heap_state) :=
  ∀ id a,
    st.(hs_allocs) !! id = Some a →
    allocation_in_range a.

(** Predicate stating that alive allocations of [st] are disjoint. *)
Definition heap_state_alloc_disjoint (st : heap_state) :=
  ∀ id1 id2 a1 a2,
    id1 ≠ id2 →
    st.(hs_allocs) !! id1 = Some a1 →
    st.(hs_allocs) !! id2 = Some a2 →
    alloc_id_alive id1 st →
    alloc_id_alive id2 st →
    a1 ## a2.

(** Predicate stating that every alive allocations in [st] has all of its
addresses mapped in the heap. *)
Definition heap_state_alloc_alive_in_heap (st : heap_state) :=
  ∀ id alloc,
    st.(hs_allocs) !! id = Some alloc →
    alloc_id_alive id st →
    ∀ a, a ∈ alloc → is_Some (st.(hs_heap) !! a).

(** Invariant on the [heap_state] maintained during evaluation. *)
Definition heap_state_invariant (st : heap_state) : Prop :=
  heap_state_heap_cell_in_range_alloc st ∧
  heap_state_heap_cell_alloc_alive st ∧
  heap_state_alloc_in_range st ∧
  heap_state_alloc_disjoint st ∧
  heap_state_alloc_alive_in_heap st.

(** ** Lemmas about the heap state invariant. *)

Lemma heap_state_alloc_alive_free_disjoint σ id a n b alloc:
  heap_state_alloc_alive_in_heap σ →
  alloc_id_alive id σ →
  heap_range_free σ.(hs_heap) a n →
  σ.(hs_allocs) !! id = Some alloc →
  Allocation a n b ## alloc.
Proof.
  move => Hin_heap Halive Hfree Hal p Hp1 Hp2.
  apply (Hin_heap _ _ Hal Halive) in Hp2 as [? Hp2].
  rewrite Hfree in Hp2; first done. apply Hp1.
Qed.

Lemma alloc_new_block_invariant σ1 σ2 l v :
  alloc_new_block σ1 l v σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  move => []; clear.
  move => σ1 l aid v alloc Haid Hfresh Halloc Hrange H.
  destruct H as (Hi1&Hi2&Hi3&Hi4&Hi5). split_and!.
  - move => a [id??] /= Ha. destruct (decide (aid = id)) as [->|Hne].
    + exists alloc. split => /=; first by rewrite lookup_insert.
      destruct (decide (l.2 ≤ a < l.2 + length v)) as [|Hne] => //=.
      exfalso. rewrite heap_update_lookup_not_in_range in Ha; last first.
      { destruct (decide (a < l.2)); [left | right] => //. lia. }
      apply Hi1 in Ha. destruct Ha as [? [Ha ?]].
      by rewrite /= Hfresh in Ha.
    + destruct (decide (a < l.2 ∨ l.2 + length v ≤ a)).
      * rewrite heap_update_lookup_not_in_range in Ha; last done.
        apply Hi1 in Ha. destruct Ha as [?[??]].
        eexists; by rewrite lookup_insert_ne.
      * exfalso. rewrite heap_update_lookup_in_range in Ha; last lia.
        by inversion Ha.
  - move => a [id??] /= Ha. destruct (decide (aid = id)) as [->|Hne].
    + exists alloc. by rewrite lookup_insert.
    + destruct (decide (a < l.2 ∨ l.2 + length v ≤ a)).
      * rewrite heap_update_lookup_not_in_range in Ha; last done.
        apply Hi2 in Ha. destruct Ha as [?[??]].
        eexists; by rewrite lookup_insert_ne.
      * exfalso. rewrite heap_update_lookup_in_range in Ha; last lia.
        by inversion Ha.
  - move => id a. destruct (decide (id = aid)) as [->|] => /=.
    + rewrite lookup_insert => ?. by simplify_eq.
    + rewrite lookup_insert_ne => //=. apply Hi3.
  - move => id1 id2 al1 al2 /= Hne Hal1 Hal2 Hid1 Hid2.
    destruct (decide (id1 = aid)) as [->|];
    last (destruct (decide (id2 = aid)) as [->|]).
    + rewrite lookup_insert in Hal1. rewrite lookup_insert_ne // in Hal2.
      simplify_eq => ???. eapply heap_state_alloc_alive_free_disjoint => //.
      move: Hid2 => /= [al []] /=. rewrite lookup_insert_ne //. by exists al.
    + rewrite lookup_insert in Hal2. rewrite lookup_insert_ne // in Hal1.
      simplify_eq => ???. eapply heap_state_alloc_alive_free_disjoint => //.
      move: Hid1 => /= [al []] /=. rewrite lookup_insert_ne //. by exists al.
    + rewrite !lookup_insert_ne // in Hal1, Hal2. move: Hid1 Hid2.
      move => [? []] /=; rewrite lookup_insert_ne // => ??.
      move => [? []] /=; rewrite lookup_insert_ne // => ??.
      apply (Hi4 id1 id2 al1 al2) => //; by eexists.
  - move => id al /= Hal [? [/= ? Halive]] a Ha. simplify_eq.
    destruct (decide (id = aid)) as [->|].
    + rewrite lookup_insert /= in Hal.
      rewrite heap_update_lookup_in_range; naive_solver.
    + rewrite lookup_insert_ne // in Hal.
      rewrite heap_update_lookup_not_in_range; last first.
      { assert (¬ (l.2 ≤ a < l.2 + length v)); last lia. move => Hin.
        assert (is_Some (hs_heap σ1 !! a)) as [? Heq].
        { eapply Hi5 => //. by eexists. }
        by rewrite Hrange in Heq. }
      eapply (Hi5 _ _ Hal); [by eexists | done |..].
Qed.

Lemma alloc_new_blocks_invariant σ1 σ2 ls vs :
  alloc_new_blocks σ1 ls vs σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  elim => [] // ??????? Hb Hbs IH H.
  apply IH. by eapply alloc_new_block_invariant.
Qed.

Lemma free_block_invariant σ1 σ2 l ly:
  free_block σ1 l ly σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  move => []; clear.
  move => σ l aid ly v al_a al_d Haid Hal_a Hlen Hlookup H.
  destruct H as (Hi1&Hi2&Hi3&Hi4&Hi5). split_and!.
  - move => a hc /= Hhc.
    assert (¬ (l.2 ≤ a < l.2 + length v)) as Hnot_in.
    { move => ?. rewrite heap_free_lookup_in_range // in Hhc; lia. }
    rewrite heap_free_lookup_not_in_range in Hhc; last lia.
    destruct (Hi1 _ _ Hhc) as [al [?[??]]]. exists al. split; last done.
    rewrite /= lookup_insert_ne; first done.
    move => ?; subst aid. simplify_eq. apply Hnot_in.
    unfold al_end in *. simpl in *. lia.
  - move => a hc /= Hhc.
    assert (¬ (l.2 ≤ a < l.2 + length v)) as Hnot_in.
    { move => ?. rewrite heap_free_lookup_in_range // in Hhc; lia. }
    rewrite heap_free_lookup_not_in_range in Hhc; last lia.
    destruct (Hi2 _ _ Hhc) as [al [??]]. exists al.
    rewrite lookup_insert_ne; first done.
    move => Heq. destruct (Hi1 _ _ Hhc) as [?[?[??]]].
    subst al_a. simplify_eq. unfold al_end in *. simpl in *. lia.
  - move => id al /=. destruct (decide (id = aid)) as [->|].
    + rewrite lookup_insert. move => [?]. subst al.
      assert (allocation_in_range al_a); last done.
      by eapply Hi3.
    + rewrite lookup_insert_ne; last done. naive_solver.
  - move => id1 id2 al1 al2 Hne /= Hid1 Hid2 Hal1 Hal2.
    destruct (decide (id1 = aid)) as [->|];
    last (destruct (decide (id2 = aid)) as [->|]).
    + rewrite lookup_insert in Hid1. rewrite lookup_insert_ne // in Hid2.
      simplify_eq. assert (al_a ## al2); last done.
      eapply (Hi4 _ _ _ _ Hne Hal_a Hid2); first by eexists.
      move: Hal2 => [?[/=]]. rewrite lookup_insert_ne //. by eexists.
    + rewrite lookup_insert in Hid2. rewrite lookup_insert_ne // in Hid1.
      simplify_eq. assert (al1 ## al_a); last done.
      eapply (Hi4 _ _ _ _ Hne Hid1 Hal_a); last by eexists.
      move: Hal1 => [?[/=]]. rewrite lookup_insert_ne //. by eexists.
    + destruct Hal1 as [a1 [Ha1 ?]]. destruct Hal2 as [a2 [Ha2 ?]].
      rewrite !lookup_insert_ne // in Hid1, Hid2, Ha1, Ha2.
      apply (Hi4 id1 id2 al1 al2) => //; by eexists.
  - move => id al /= Hid [?[Hal1 Hal2]] a Ha. assert (id ≠ aid) as ?.
    { move => ?; subst id. rewrite lookup_insert in Hal1. naive_solver. }
    rewrite lookup_insert_ne // in Hid, Hal1. simplify_eq.
    rewrite heap_free_lookup_not_in_range;
    first (eapply Hi5 => //; by eexists). move => ?.
    assert (al ## al_a) as Hdisj.
    { apply (Hi4 _ _ _ _ H Hid Hal_a); by eexists. }
    erewrite elem_of_disjoint in Hdisj. by eapply Hdisj.
Qed.

Lemma free_blocks_invariant σ1 σ2 ls:
  free_blocks σ1 ls σ2 →
  heap_state_invariant σ1 →
  heap_state_invariant σ2.
Proof.
  elim => [] // ?????? Hb Hbs IH H.
  apply IH. by eapply free_block_invariant.
Qed.

Lemma heap_update_heap_cell_in_range_alloc σ a v1 v2 Paid Plk faid flk:
  heap_state_heap_cell_in_range_alloc σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_heap_cell_in_range_alloc {|
    hs_heap := heap_update a v2 faid flk σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  elim: v2 v1 a => // b2 v2 IH [] // b1 v1 a1 Hσ Hcontains Hfaid [] Hlen.
  move => a2 hc H /=. rewrite /heap_lookup -/heap_lookup in Hcontains.
  move: Hcontains => [[id[?[Heq [??]]]] Hcontains].
  destruct (decide (a1 = a2)) as [->|Hne].
  - rewrite lookup_partial_alter -/heap_update in H. simplify_eq => /=.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Heq /= Hfaid.
    apply (Hσ a2 _ Heq).
  - rewrite lookup_partial_alter_ne // -/heap_update in H.
    by unshelve eapply (IH _ _ Hσ _ Hfaid Hlen a2 hc) => //.
Qed.

Lemma heap_update_heap_cell_alloc_alive σ a v1 v2 Paid Plk faid flk:
  heap_state_heap_cell_alloc_alive σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_heap_cell_alloc_alive {|
    hs_heap := heap_update a v2 faid flk σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  elim: v2 v1 a => // b2 v2 IH [] // b1 v1 a1 Hσ Hcontains Hfaid [] Hlen.
  move => a2 hc H /=. rewrite /heap_lookup -/heap_lookup in Hcontains.
  move: Hcontains => [[id[?[Heq [??]]]] Hcontains].
  destruct (decide (a1 = a2)) as [->|Hne].
  - rewrite lookup_partial_alter -/heap_update in H. simplify_eq => /=.
    rewrite heap_update_lookup_not_in_range; last lia. rewrite Heq /= Hfaid.
    apply (Hσ a2 _ Heq).
  - rewrite lookup_partial_alter_ne // -/heap_update in H.
    by unshelve eapply (IH _ _ Hσ _ Hfaid Hlen a2 hc) => //.
Qed.

Lemma heap_update_alloc_alive_in_heap σ a v1 v2 Paid Plk faid flk:
  heap_state_alloc_alive_in_heap σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_alloc_alive_in_heap {|
    hs_heap := heap_update a v2 faid flk σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  move => H Hlookup Hfaid Hlen id al /= Hal Halive p Hp.
  destruct (decide (a ≤ p < a + length v2)).
  - rewrite heap_update_lookup_in_range //=. by eexists.
  - rewrite heap_update_lookup_not_in_range; last lia. by eapply H.
Qed.

Lemma heap_update_heap_state_invariant σ a v1 v2 Paid Plk faid flk:
  heap_state_invariant σ →
  heap_lookup a v1 Paid Plk σ.(hs_heap) →
  (∀ aid, faid (Some aid) = aid) →
  length v1 = length v2 →
  heap_state_invariant {|
    hs_heap := heap_update a v2 faid flk σ.(hs_heap);
    hs_allocs := σ.(hs_allocs);
  |}.
Proof.
  move => [?[?[?[??]]]] ???. split_and!.
  - by eapply heap_update_heap_cell_in_range_alloc.
  - by eapply heap_update_heap_cell_alloc_alive.
  - move => *. naive_solver.
  - move => *. naive_solver.
  - by eapply heap_update_alloc_alive_in_heap.
Qed.
