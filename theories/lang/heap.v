From stdpp Require Import coPset.
From iris.algebra Require Import big_op gmap frac agree.
From iris.algebra Require Import csum excl auth cmra_big_op numbers.
From iris.bi Require Import fractional.
From iris.base_logic Require Export lib.own.
From iris.proofmode Require Export tactics.
From refinedc.lang Require Export lang.
Set Default Proof Using "Type".
Import uPred.

Definition lock_stateR : cmraT :=
  csumR (exclR unitO) natR.

Definition heapUR : ucmraT :=
  gmapUR loc (prodR (prodR fracR lock_stateR) (agreeR mbyteO)).

Definition allocR : cmraT :=
  agreeR allocationO.

Definition allocsUR : ucmraT :=
  gmapUR Z allocR.

Definition fntblUR : ucmraT :=
  gmapUR loc (agreeR functionO).

Class heapG Σ := HeapG {
  heap_inG :> inG Σ (authR heapUR);
  heap_name : gname;
  heap_allocs_inG :> inG Σ (authR allocsUR);
  heap_allocs_name : gname;
  heap_fntbl_inG :> inG Σ (authR fntblUR);
  heap_fntbl_name : gname;
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.

Definition to_heap : heap → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).

Definition to_alloc (a : allocation) : allocR :=
  to_agree a.

Definition to_allocs : gmap alloc_id allocation → allocsUR :=
  fmap to_alloc.

Definition to_fntbl : gmap loc function → fntblUR :=
  fmap to_agree.

Section definitions.
  Context `{!heapG Σ}.

  Implicit Types (st : lock_state) (l : loc) (q : Qp) (b : mbyte).

  Definition allocs_entry_def (id : alloc_id) (a : allocation) : iProp Σ :=
    own heap_allocs_name (◯ {[ id := to_alloc a ]}).
  Definition allocs_entry_aux : seal (@allocs_entry_def). by eexists. Qed.
  Definition allocs_entry := unseal allocs_entry_aux.
  Definition allocs_entry_eq : @allocs_entry = @allocs_entry_def :=
    seal_eq allocs_entry_aux.

  Definition loc_in_bounds_def (l : loc) (n : nat) : iProp Σ :=
    ∃ a, ⌜alloc_start a ≤ l.2 ∧ l.2 + n ≤ alloc_end a⌝ ∗ allocs_entry (fst l) a.
  Definition loc_in_bounds_aux : seal (@loc_in_bounds_def). by eexists. Qed.
  Definition loc_in_bounds := unseal loc_in_bounds_aux.
  Definition loc_in_bounds_eq : @loc_in_bounds = @loc_in_bounds_def :=
    seal_eq loc_in_bounds_aux.

  Definition heap_mapsto_mbyte_st st l q b : iProp Σ :=
    own heap_name (◯ {[ l := (q, to_lock_stateR st, to_agree b) ]}).

  Definition heap_mapsto_mbyte_def l q b : iProp Σ :=
    heap_mapsto_mbyte_st (RSt 0) l q b.

  Definition heap_mapsto_mbyte_aux : seal (@heap_mapsto_mbyte_def). by eexists. Qed.
  Definition heap_mapsto_mbyte := unseal heap_mapsto_mbyte_aux.
  Definition heap_mapsto_mbyte_eq : @heap_mapsto_mbyte = @heap_mapsto_mbyte_def :=
    seal_eq heap_mapsto_mbyte_aux.

  Definition heap_mapsto_def (l : loc) (q : Qp) (v : val) : iProp Σ :=
    loc_in_bounds l (length v) ∗ ([∗ list] i ↦ b ∈ v, heap_mapsto_mbyte (l +ₗ i) q b)%I.
  Definition heap_mapsto_aux : seal (@heap_mapsto_def). by eexists. Qed.
  Definition heap_mapsto := unseal heap_mapsto_aux.
  Definition heap_mapsto_eq : @heap_mapsto = @heap_mapsto_def :=
    seal_eq heap_mapsto_aux.

  Definition fntbl_entry_def (l : loc) (f: function) : iProp Σ :=
    own heap_fntbl_name (◯ {[ l := to_agree f ]}).
  Definition fntbl_entry_aux : seal (@fntbl_entry_def). by eexists. Qed.
  Definition fntbl_entry := unseal fntbl_entry_aux.
  Definition fntbl_entry_eq : @fntbl_entry = @fntbl_entry_def :=
    seal_eq fntbl_entry_aux.

  Definition heap_ctx (h : heap) : iProp Σ :=
    (own heap_name (● to_heap h))%I.

  Definition allocs_ctx (ub : allocs) : iProp Σ :=
    (own heap_allocs_name (● to_allocs ub))%I.

  Definition fntbl_ctx (t : gmap loc function) : iProp Σ :=
    (own heap_fntbl_name (● to_fntbl t))%I.

  Definition blocks_used_agree (h : heap) (ub : allocs) : Prop :=
    ∀ l, ub !! l.1 = None → heap_block_free h l.

  Definition state_ctx (σ:state) : iProp Σ :=
    ⌜blocks_used_agree σ.(st_heap) σ.(st_allocs)⌝ ∗
    heap_ctx σ.(st_heap) ∗
    allocs_ctx σ.(st_allocs) ∗
    fntbl_ctx σ.(st_fntbl).
End definitions.

Typeclasses Opaque heap_mapsto_mbyte heap_mapsto.

Notation "l ↦{ q } v" := (heap_mapsto l q v)
  (at level 20, q at level 50, format "l  ↦{ q }  v") : bi_scope.
Notation "l ↦ v" := (heap_mapsto l 1 v) (at level 20) : bi_scope.
Notation "l ↦{ q '}' ':' P" := (∃ v, l ↦{ q } v ∗ P v)%I
  (at level 20, q at level 50, format "l  ↦{ q '}' ':'  P") : bi_scope.
Notation "l ↦: P " := (∃ v, l ↦ v ∗ P v)%I
  (at level 20, format "l  ↦:  P") : bi_scope.

Definition heap_mapsto_layout `{!heapG Σ} (l : loc) (q : Qp) (ly : layout) : iProp Σ :=
  (∃ v, ⌜v `has_layout_val` ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ l ↦{q} v).
Notation "l ↦{ q }| ly |" := (heap_mapsto_layout l q ly)
  (at level 20, q at level 50, format "l  ↦{ q }| ly |") : bi_scope.
Notation "l ↦| ly | " := (heap_mapsto_layout l 1%Qp ly)
  (at level 20, format "l  ↦| ly |") : bi_scope.

Section to_heap.
  Implicit Types h : heap.

  Lemma to_heap_valid h : ✓ to_heap h.
  Proof. intros l. rewrite lookup_fmap. by case (h !! l) => // -[[]?]. Qed.

  Lemma lookup_to_heap_None h l : h !! l = None → to_heap h !! l = None.
  Proof. by rewrite /to_heap lookup_fmap=> ->. Qed.

  Lemma to_heap_insert h l v x:
    to_heap (<[l:=(x, v)]> h)
    = <[l:=(1%Qp, to_lock_stateR x, to_agree v)]> (to_heap h).
  Proof. by rewrite /to_heap fmap_insert. Qed.

  Lemma to_heap_delete h l : to_heap (delete l h) = delete l (to_heap h).
  Proof. by rewrite /to_heap fmap_delete. Qed.
End to_heap.

Section to_allocs.
  Implicit Types b : allocs.

  Lemma to_allocs_valid b : ✓ to_allocs b.
  Proof. intros id. rewrite lookup_fmap. by case (b !! id) => // -[[]?]. Qed.
End to_allocs.

Section fntbl.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Lemma to_fntbl_valid f : ✓ to_fntbl f.
  Proof. intros l. rewrite lookup_fmap. by case (f !! l). Qed.

  Lemma to_fntbl_insert f l v :
    to_fntbl (<[l:=v]> f) = <[l:=to_agree v]> (to_fntbl f).
  Proof. by rewrite /to_fntbl fmap_insert. Qed.

  Lemma lookup_to_fntbl_None f l : f !! l = None → to_fntbl f !! l = None.
  Proof. by rewrite /to_fntbl lookup_fmap=> ->. Qed.

  Global Instance fntbl_entry_pers f fn : Persistent (fntbl_entry f fn).
  Proof. rewrite fntbl_entry_eq. by apply _. Qed.

  Lemma fntbl_entry_lookup t f fn :
    fntbl_ctx t -∗ fntbl_entry f fn -∗ ⌜t !! f = Some fn⌝.
  Proof.
    rewrite fntbl_entry_eq. iIntros "Htbl Hf".
    iDestruct (own_valid_2 with "Htbl Hf") as %[Hf?]%auth_both_valid_discrete.
    iPureIntro. move: Hf=> /singleton_included_l [f'].
    rewrite lookup_fmap fmap_Some_equiv => [[[f'' [? ->]]]] /Some_included_total /to_agree_included.
    by intros ->%leibniz_equiv.
  Qed.

End fntbl.

Section blocks_used_agree.

  Lemma blocks_used_agree_heap_upd l v v2 f f2 ly h ub:
    heap_at l ly v2 f2 h →
    blocks_used_agree h ub →
    length v = length v2 → blocks_used_agree (heap_upd l v f h) ub.
  Proof.
    destruct v, v2 => //. move: ly => -[[|?] ?] [?[?]]// [[?[??]]?].
    move => Hused Hlen l' Hl' o. rewrite heap_upd_lookup_ne. by apply Hused.
    move => Heq. cut (h !! (l +ₗ 0) = None). rewrite shift_loc_0. naive_solver.
    apply Hused. by rewrite Heq.
  Qed.

  Lemma blocks_used_agree_heap_free_list ls ub h:
    blocks_used_agree h ub → blocks_used_agree (heap_free_list ls h) ub.
  Proof.
    move => Hub l Hl. apply heap_block_free_free_list. by apply Hub.
  Qed.

  Lemma blocks_used_agree_heap_upd_list_in ls vs f ub h:
    list_to_set ls.*1 ⊆ dom (gset alloc_id) ub →
    blocks_used_agree h ub → blocks_used_agree (heap_upd_list ls vs f h) ub.
  Proof.
    move => Hls Hb l Hl. apply heap_block_free_upd_list; first by apply Hb.
    assert (l.1 ∉ dom (gset alloc_id) ub); last by set_solver.
    by rewrite elem_of_dom Hl.
  Qed.

  Lemma blocks_used_agree_update l v h flk allocs:
    blocks_used_agree h allocs →
    allocs !! l.1 = None →
    heap_block_free h l →
    blocks_used_agree (heap_upd l v flk h) (<[l.1:=to_allocation l.2 (length v)]> allocs).
  Proof.
    move => Hagree Hnone Hfree l' /lookup_insert_None[??] ?.
    rewrite heap_upd_lookup_ne //. by apply: Hagree.
  Qed.
End blocks_used_agree.

Section allocs.
  Context `{!heapG Σ}.

  Global Instance allocs_entry_pers b a : Persistent (allocs_entry b a).
  Proof. rewrite allocs_entry_eq. by apply _. Qed.

  Global Instance alloc_entry_timeless b a : Timeless (allocs_entry b a).
  Proof. rewrite allocs_entry_eq. by apply _. Qed.

  Lemma allocs_entry_agree b a1 a2 :
    allocs_entry b a1 -∗ allocs_entry b a2 -∗ ⌜a1 = a2⌝.
  Proof.
    move: a1 a2 => ? ?. rewrite allocs_entry_eq /allocs_entry_def.
    iIntros "H1 H2". iCombine "H1 H2" as "H".
    iDestruct (own_valid with "H") as %Hvalid.
    by move: Hvalid => /auth_frag_valid/singleton_valid/to_agree_op_inv_L.
  Qed.

  Lemma allocs_alloc ub id a :
    ub !! id = None →
    allocs_ctx ub ==∗ allocs_ctx (<[id := a]> ub) ∗ allocs_entry id a.
  Proof.
    move => Hid. rewrite /allocs_ctx allocs_entry_eq /allocs_entry_def.
    rewrite -own_op. apply own_update, auth_update_alloc.
    rewrite /to_allocs fmap_insert.
    apply alloc_singleton_local_update; last done.
    by rewrite lookup_fmap Hid.
  Qed.

  Lemma allocs_entry_to_loc_in_bounds l (n : nat) a:
    alloc_start a ≤ l.2 ∧ l.2 + n ≤ alloc_end a ->
    allocs_entry l.1 a -∗ loc_in_bounds l n.
  Proof.
    iIntros (?) "?". rewrite loc_in_bounds_eq/loc_in_bounds_def. iExists _. by iFrame.
  Qed.

  Lemma allocs_alloc_list (ls : list loc) (vs : list val) (ub : allocs):
    NoDup ls.*1 ->
    dom (gset _) ub ## (list_to_set ls.*1) →
    length vs = length ls →
    allocs_ctx ub ==∗
      allocs_ctx (list_to_map (zip ls.*1 (zip_with to_allocation ls.*2 (length <$> vs))) ∪ ub) ∗
      ([∗ list] l;v ∈ ls;vs, loc_in_bounds l (length v)).
  Proof.
    elim: ls vs.
    - move => [] // _ _ _ /=. rewrite left_id. by iIntros "$".
    - move => [id off] ls IH [|v vs] //. csimpl. move => /NoDup_cons [??] Hdisj Hlen.
      iIntros "H". iMod (IH vs with "H") as "[H $]"; [done | set_solver | lia | ..].
      iMod (allocs_alloc _ id (Allocation off (off + length v)) with "H") as "[H1 H2]".
      { apply lookup_union_None. split; last by (apply not_elem_of_dom; set_solver).
        apply not_elem_of_list_to_map. rewrite fst_zip // zip_with_length !fmap_length.
        rewrite Min.min_l //. simplify_eq. by rewrite Hlen. }
      iSplitR "H2"; first by rewrite insert_union_l.
      iModIntro.
      by iApply allocs_entry_to_loc_in_bounds => //=.
  Qed.

  Lemma allocs_entry_lookup t b a :
    allocs_ctx t -∗ allocs_entry b a -∗ ⌜t !! b = Some a⌝.
  Proof.
    rewrite allocs_entry_eq. iIntros "Htbl Hf".
    iDestruct (own_valid_2 with "Htbl Hf") as %[Hf?]%auth_both_valid_discrete.
    iPureIntro. move: Hf=> /singleton_included_l [f'].
    rewrite lookup_fmap fmap_Some_equiv => [[[f'' [? ->]]]] /Some_included_total /to_agree_included.
    by intros ->%leibniz_equiv.
  Qed.
End allocs.

Section loc_in_bounds.
  Context `{!heapG Σ}.

  Global Instance loc_in_bounds_pers l n : Persistent (loc_in_bounds l n).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  Global Instance loc_in_bounds_timeless l n : Timeless (loc_in_bounds l n).
  Proof. rewrite loc_in_bounds_eq. by apply _. Qed.

  Lemma loc_in_bounds_split l n m :
    loc_in_bounds l n ∗ loc_in_bounds (l +ₗ n) m ⊣⊢ loc_in_bounds l (n + m).
  Proof.
    rewrite loc_in_bounds_eq.
    iSplit.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (a [Hstart ?]) "#H1".
      iDestruct "H2" as (? [?   Hend]) "#H2".
      iDestruct (allocs_entry_agree with "H2 H1") as %->.
      iExists a. iFrame "H1". iPureIntro. simpl in Hend. lia.
    - iIntros "H". iDestruct "H" as (a [??]) "#H".
      iSplit; iExists a; iFrame "H"; iPureIntro; simpl; lia.
  Qed.

  Lemma loc_in_bounds_split_mul_S l n m :
    loc_in_bounds l n ∗ loc_in_bounds (l +ₗ n) (n * m) ⊣⊢ loc_in_bounds l (n * S m).
  Proof.
    have ->: (n * S m = n + n * m)%nat by lia.
    etrans; [ by apply loc_in_bounds_split | done ].
  Qed.

  Lemma loc_in_bounds_shorten l n m:
    (m ≤ n)%nat ->
    loc_in_bounds l n -∗ loc_in_bounds l m.
  Proof. move => ?. rewrite (le_plus_minus m n) // -loc_in_bounds_split. iIntros "[$ _]". Qed.

  Lemma loc_in_bounds_to_heap_loc_in_bounds l σ n:
    loc_in_bounds l n -∗ state_ctx σ -∗ ⌜heap_loc_in_bounds l n σ⌝.
  Proof.
    rewrite loc_in_bounds_eq.
    iIntros "Hb (?&?&Hctx&?)". iDestruct "Hb" as (a Ha) "Hb".
    iExists a. iSplit; last done.
    by iApply (allocs_entry_lookup with "Hctx").
  Qed.
End loc_in_bounds.

Section heap.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Global Instance heap_mapsto_mbyte_timeless l q v : Timeless (heap_mapsto_mbyte l q v).
  Proof.  rewrite heap_mapsto_mbyte_eq. apply _. Qed.

  Global Instance heap_mapsto_mbyte_fractional l v: Fractional (λ q, heap_mapsto_mbyte l q v)%I.
  Proof.
    intros p q.
    by rewrite heap_mapsto_mbyte_eq -own_op -auth_frag_op singleton_op -pair_op agree_idemp.
  Qed.

  Global Instance heap_mapsto_mbyte_as_fractional l q v:
    AsFractional (heap_mapsto_mbyte l q v) (λ q, heap_mapsto_mbyte l q v)%I q.
  Proof. split. done. apply _. Qed.

  Global Instance heap_mapsto_timeless l q v : Timeless (l↦{q}v).
  Proof.  rewrite heap_mapsto_eq. apply _. Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. rewrite heap_mapsto_eq. apply _. Qed.

  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma heap_mapsto_loc_in_bounds l q v:
    l ↦{q} v -∗ loc_in_bounds l (length v).
  Proof. rewrite heap_mapsto_eq. iIntros "[$ _]". Qed.

  Lemma heap_mapsto_loc_in_bounds_0 l q v:
    l ↦{q} v -∗ loc_in_bounds l 0.
  Proof. iIntros "Hl". iApply loc_in_bounds_shorten; [ | by iApply heap_mapsto_loc_in_bounds]. lia. Qed.

  Lemma heap_mapsto_nil l q:
    l ↦{q} [] ⊣⊢ loc_in_bounds l 0.
  Proof. rewrite heap_mapsto_eq/heap_mapsto_def /=. solve_sep_entails. Qed.

  Lemma heap_mapsto_cons_mbyte l b v q:
    l ↦{q} (b::v) ⊣⊢ heap_mapsto_mbyte l q b ∗ loc_in_bounds l 1 ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_mapsto_eq/heap_mapsto_def /= shift_loc_0. setoid_rewrite shift_loc_assoc.
    have Hn:(∀ n, Z.of_nat (S n) = 1 + n) by lia. setoid_rewrite Hn.
    have ->:(∀ n, S n = 1 + n)%nat by lia.
    rewrite -loc_in_bounds_split.
    solve_sep_entails.
  Qed.

  Lemma heap_mapsto_cons l b v q:
    l ↦{q} (b::v) ⊣⊢ l ↦{q} [b] ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite heap_mapsto_cons_mbyte !assoc. f_equiv.
    rewrite heap_mapsto_eq/heap_mapsto_def /= shift_loc_0.
    solve_sep_entails.
  Qed.

  Lemma heap_mapsto_app l v1 v2 q:
    l ↦{q} (v1 ++ v2) ⊣⊢ l ↦{q} v1 ∗ (l +ₗ length v1) ↦{q} v2.
  Proof.
    elim: v1 l.
    - move => l /=. rewrite heap_mapsto_nil shift_loc_0.
      iSplit; [ iIntros "Hl" | by iIntros "[_ $]" ].
      iSplit => //. by iApply heap_mapsto_loc_in_bounds_0.
    - move => b v1 IH l /=.
      rewrite heap_mapsto_cons IH assoc -heap_mapsto_cons.
      rewrite shift_loc_assoc.
      by have ->:(∀ n : nat, 1 + n = S n) by lia.
  Qed.

  Lemma heap_mapsto_mbyte_agree l q1 q2 v1 v2 : heap_mapsto_mbyte l q1 v1 ∗ heap_mapsto_mbyte l q2 v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_mbyte_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /to_agree_op_inv_L->]; eauto.
  Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 :
    length v1 = length v2 →
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    elim: v1 v2 l. by iIntros ([] ??)"??".
    move => ?? IH []//=???[?].
    rewrite !heap_mapsto_cons_mbyte.
    iIntros "[? [_ ?]] [? [_ ?]]".
    iDestruct (IH with "[$] [$]") as %-> => //.
    by iDestruct (heap_mapsto_mbyte_agree with "[$]") as %->.
  Qed.

  Lemma heap_alloc l h v :
    heap_block_free h l ->
    heap_ctx h ∗ loc_in_bounds l (length v) ==∗
      heap_ctx (heap_upd l v (λ _, RSt 0%nat) h) ∗ l ↦ v.
  Proof.
    rewrite /heap_block_free => Hfree.
    have [->|Hv] := decide(v = []).
    { iIntros "[$ ?] !#" => /=. by iApply heap_mapsto_nil. }
    rewrite heap_mapsto_eq/heap_mapsto_def heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def.
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) /=.
    iIntros "[H $]". rewrite -own_op. iApply own_update; last done.
    apply auth_update_alloc.
    elim: v l Hfree {Hv} => // b bl IH l Hfree.
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= shift_loc_0.
    etrans. 1: by apply (IH (l +ₗ 1)); intros; rewrite shift_loc_assoc.
    rewrite -insert_singleton_op; last first.
    { rewrite -equiv_None big_opL_commute equiv_None big_opL_None=> l' v' ?.
      rewrite lookup_singleton_None -{2}(shift_loc_0 l). apply not_inj; lia. }
    rewrite to_heap_insert. setoid_rewrite shift_loc_assoc.
    apply alloc_local_update; last done. apply lookup_to_heap_None.
    rewrite heap_upd_lookup_lt; last lia. by rewrite -(shift_loc_0 l).
  Qed.

  Lemma heap_alloc_list ls vs h :
    Forall (heap_block_free h) ls ->
    NoDup ls.*1 ->
    length vs = length ls →
    heap_ctx h ∗ ([∗ list] l;v ∈ ls;vs, loc_in_bounds l (length v)) ==∗
      heap_ctx (heap_upd_list ls vs (λ _, RSt 0%nat) h) ∗ ([∗ list] l;v ∈ ls;vs, l ↦ v).
  Proof.
    elim: ls vs; first by move => [] /=; iIntros.
    move => l ls IH [|v vs] //. csimpl => /Forall_cons[??] /NoDup_cons[??] [?].
    iIntros "[Hown [Hinbl Hinbls]]".
    iMod (IH vs with "[Hown Hinbls]") as "[Hown $]" => //; first by iFrame.
    iApply (heap_alloc with "[Hown Hinbl]"); last by iFrame.
    by apply heap_block_free_upd_list.
  Qed.

  Lemma heap_mapsto_mbyte_lookup_q ls l h q b:
    heap_ctx h -∗
    heap_mapsto_mbyte_st ls l q b -∗
    ⌜∃ n' : nat,
        h !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]]]; simplify_eq.
    move=> /Some_pair_included_total_2
      [/Some_pair_included [_ Hincl] /to_agree_included->].
    destruct ls as [|n], ls'' as [|n''],
       Hincl as [[[|n'|]|] [=]%leibniz_equiv]; subst.
    by exists O. eauto. exists O. by rewrite Nat.add_0_r.
  Qed.

  Lemma heap_mapsto_mbyte_lookup_1 ls l h b:
    heap_ctx h -∗
    heap_mapsto_mbyte_st ls l 1%Qp b -∗
    ⌜h !! l = Some (ls, b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid_discrete.
    iPureIntro. move: Hl=> /singleton_included_l [[[q' ls'] dv]].
    rewrite /to_heap lookup_fmap fmap_Some_equiv.
    move=> [[[ls'' v'] [?[[/=??]->]]] Hincl]; simplify_eq.
    apply (Some_included_exclusive _ _) in Hincl as [? Hval]; last by destruct ls''.
    apply (inj to_agree) in Hval. fold_leibniz. subst.
    destruct ls, ls''; rewrite ?Nat.add_0_r; naive_solver.
  Qed.

  Lemma heap_mapsto_lookup_q flk l h q v:
    (∀ n, flk (RSt n) : Prop) →
    heap_ctx h -∗ l ↦{q} v -∗ ⌜heap_at_go l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]".
    iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n Hn]. by eauto.
  Qed.

  Lemma heap_mapsto_lookup_1 (flk : lock_state → Prop) l h v:
    flk (RSt 0%nat) →
    heap_ctx h -∗ l ↦ v -∗ ⌜heap_at_go l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq /=.
    iDestruct "Hl" as "[Hb [_ Hl]]".
    iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as %Hl. by eauto.
  Qed.

  Lemma heap_read_mbyte_vs h n1 n2 nf l q b:
    h !! l = Some (RSt (n1 + nf), b) →
    heap_ctx h -∗ heap_mapsto_mbyte_st (RSt n1) l q b
    ==∗ heap_ctx (<[l:=(RSt (n2 + nf), b)]> h)
        ∗ heap_mapsto_mbyte_st (RSt n2) l q b.
  Proof.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply prod_local_update_1, prod_local_update_2, csum_local_update_r.
    apply nat_local_update; lia.
  Qed.

  Lemma heap_read_na h l q v :
    heap_ctx h -∗ l ↦{q} v ==∗
      ⌜heap_at_go l v (λ st, ∃ n, st = RSt n) h⌝ ∗
      heap_ctx (heap_upd l v (λ st, if st is Some (RSt n) then RSt (S n) else WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_at_go l v (λ st, ∃ n, st = RSt (S n)) h2⌝ ∗
        heap_ctx (heap_upd l v (λ st, if st is Some (RSt (S n)) then RSt n else WSt) h2) ∗ l ↦{q} v.
  Proof.
    iIntros "Hh Hv".
    iDestruct (heap_mapsto_lookup_q with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l Hat) => //=.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    rewrite ->heap_mapsto_cons_mbyte, heap_mapsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [? Hl]]".
    move: Hat => /= -[[? [Hin [n ?]]] ?]; subst.
    iMod ("IH" with "[] Hh Hl") as "{IH}[Hh IH]" => //.
    iMod (heap_read_mbyte_vs _ 0 1 with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    iModIntro. iSplitL "Hh".
    { iStopProof. f_equiv. symmetry. apply partial_alter_to_insert. by rewrite heap_upd_lookup_lt // Hin. }
    iIntros (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n' Hn].
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]".
    iSplitR; first by iPureIntro; naive_solver.
    iMod (heap_read_mbyte_vs _ 1 0 with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq. iFrame. iModIntro.
    { iStopProof. f_equiv. symmetry. apply partial_alter_to_insert. by rewrite heap_upd_lookup_lt // Hn. }
  Qed.

  Lemma heap_write_mbyte_vs h st1 st2 l b b':
    h !! l = Some (st1, b) →
    heap_ctx h -∗ heap_mapsto_mbyte_st st1 l 1%Qp b
    ==∗ heap_ctx (<[l:=(st2, b')]> h) ∗ heap_mapsto_mbyte_st st2 l 1%Qp b'.
  Proof.
    intros Hσv. apply wand_intro_r. rewrite -!own_op to_heap_insert.
    eapply own_update, auth_update, singleton_local_update.
    { by rewrite /to_heap lookup_fmap Hσv. }
    apply exclusive_local_update. by destruct st2.
  Qed.

  Lemma heap_write f h l v v':
    length v = length v' → f (Some (RSt 0)) = RSt 0 →
    heap_ctx h -∗ l ↦ v ==∗ heap_ctx (heap_upd l v' f h) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen Hf) "Hh Hmt".
    iInduction (v) as [|v b] "IH" forall (l v' Hlen); destruct v' => //; first by iFrame.
    move: Hlen => [] Hlen. rewrite !heap_mapsto_cons_mbyte !heap_mapsto_mbyte_eq.
    iDestruct "Hmt" as "[Hb [Hinb Hl]]".
    iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as % Hin; auto.
    iMod ("IH" with "[//] Hh Hl") as "[Hh $]".
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh $]". by rewrite heap_upd_lookup_lt.
    iModIntro => /=. iClear "IH". iFrame "Hinb". iStopProof. f_equiv => /=. symmetry.
    apply: partial_alter_to_insert.
    by rewrite heap_upd_lookup_lt // Hin Hf.
  Qed.

  Lemma heap_write_na h l v v' :
    length v = length v' →
    heap_ctx h -∗ l ↦ v ==∗
      ⌜heap_at_go l v (λ st, st = RSt 0) h⌝ ∗
      heap_ctx (heap_upd l v (λ _, WSt) h) ∗
      ∀ h2, heap_ctx h2 ==∗ ⌜heap_at_go l v (λ st, st = WSt) h2⌝ ∗
        heap_ctx (heap_upd l v' (λ _, RSt 0) h2) ∗ l ↦ v'.
  Proof.
    iIntros (Hlen) "Hh Hv".
    iDestruct (heap_mapsto_lookup_1 with "Hh Hv") as %Hat. 2: iSplitR => //. 1: by naive_solver.
    iInduction (v) as [|b v] "IH" forall (l v' Hat Hlen) => //=; destruct v' => //.
    { iFrame. by iIntros "!#" (?) "$ !#". }
    move: Hlen => -[] Hlen.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq.
    iDestruct "Hv" as "[Hb [? Hl]]".
    move: Hat => /= -[[? [Hin ?]] ?]; subst.
    iMod ("IH" with "[] [] Hh Hl") as "{IH}[Hh IH]" => //.
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    iFrame. iIntros "!#" (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as %Hn.
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]".
    iSplitR; first by iPureIntro; naive_solver.
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt. iFrame.
    rewrite heap_mapsto_cons_mbyte heap_mapsto_mbyte_eq. by iFrame.
  Qed.

  Lemma heap_free_free l ly h :
    heap_ctx h -∗ l ↦|ly| ==∗ heap_ctx (heap_free l ly.(ly_size) h).
  Proof.
    iIntros "Hown". iDestruct 1 as (v <- _) "Hl".
    have [->|Hv] := decide(v = []). done.
    rewrite heap_mapsto_eq/heap_mapsto_def heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def.
    iDestruct "Hl" as "[_ Hl]".
    iStopProof.
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) -own_op.
    apply own_update, auth_update_dealloc.
    elim: v l h {Hv} => // b bl IH l h.
    rewrite (big_opL_consZ_l (λ k _, _ (_ k) _ )) /= shift_loc_0.
    apply local_update_total_valid=> _ Hvalid _.
    have ? : (([^op list] k↦y ∈ bl, {[l +ₗ (1 + k) := (1%Qp, to_lock_stateR (RSt 0%nat), to_agree y)]} : heapUR) !! l = None). {
      move: (Hvalid l). rewrite lookup_op lookup_singleton.
      by move=> /(cmra_discrete_valid_iff 0) /exclusiveN_Some_l.
    }
    rewrite -insert_singleton_op //.
    etrans. { apply (delete_local_update _ _ l (1%Qp, to_lock_stateR (RSt 0%nat), to_agree b)). by rewrite lookup_insert. }
    rewrite delete_insert // -to_heap_delete heap_free_delete.
    setoid_rewrite <-shift_loc_assoc. by apply IH.
  Qed.

  Lemma heap_free_list_free ls lys h :
    heap_ctx h -∗ ([∗ list] l;ly ∈ ls;lys, l ↦|ly|) ==∗
        heap_ctx (heap_free_list (zip ls lys) h).
  Proof.
    elim: ls lys. by iIntros (?) "$ _ !#".
    move => l ls IH [|ly lys]; csimpl. by iIntros "? ?".
    iIntros "Hown [Hl Hls]".
    iMod (IH lys with "Hown Hls") as "Hown" => //.
    by iApply (heap_free_free with "Hown").
  Qed.
End heap.

Section alloc_new_blocks.
  Context `{!heapG Σ}.

  Lemma heap_alloc_new_block_upd σ1 l v σ2:
    alloc_new_block σ1 l v σ2 →
    state_ctx σ1 ==∗
      state_ctx σ2 ∗
      allocs_entry l.1 (to_allocation l.2 (length v)) ∗
      l ↦ v.
  Proof.
    iIntros (Halloc) "Hctx". iDestruct "Hctx" as (Hagree) "(Hhctx&Hbctx&Hfctx)".
    inversion_clear Halloc.
    iMod (allocs_alloc (st_allocs σ1) l.1 (to_allocation l.2 (length v))
            with "Hbctx") as "[Hbctx Hb]"; first done.
    iDestruct (allocs_entry_to_loc_in_bounds l (length v)
                 with "Hb") as "#Hinb"; first by naive_solver.
    iMod (heap_alloc l (st_heap σ1) v with "[Hhctx $Hinb]") as "[Hhctx Hv]" => //.
    iModIntro. iFrame. iPureIntro => /=. by apply blocks_used_agree_update.
  Qed.

  Lemma heap_alloc_new_blocks_upd σ1 ls vs σ2:
    alloc_new_blocks σ1 ls vs σ2 →
    state_ctx σ1 ==∗
      state_ctx σ2 ∗
      ([∗ list] l; v ∈ ls; vs, allocs_entry l.1 (to_allocation l.2 (length v))) ∗
      ([∗ list] l; v ∈ ls; vs, l ↦ v).
  Proof.
    move => H. iInduction H as [] "IH"; first by iIntros "$ !>" => //=.
    iIntros "H". iMod (heap_alloc_new_block_upd with "H") as "(H&Ha&Hl)" => //.
    iFrame. by iApply "IH".
  Qed.
End alloc_new_blocks.
