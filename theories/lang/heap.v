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

Definition fntblUR : ucmraT :=
  gmapUR loc (agreeR functionO).

Class heapG Σ := HeapG {
  heap_inG :> inG Σ (authR heapUR);
  heap_name : gname;
  heap_fntbl_inG :> inG Σ (authR fntblUR);
  heap_fntbl_name : gname;
}.

Definition to_lock_stateR (x : lock_state) : lock_stateR :=
  match x with RSt n => Cinr n | WSt => Cinl (Excl ()) end.
Definition to_heap : heap → heapUR :=
  fmap (λ v, (1%Qp, to_lock_stateR (v.1), to_agree (v.2))).

Definition to_fntbl : gmap loc function → fntblUR :=
  fmap (λ v, to_agree (v)).

Section definitions.
  Context `{!heapG Σ}.

  Definition heap_mapsto_mbyte_st (st : lock_state)
             (l : loc) (q : Qp) (b: mbyte) : iProp Σ :=
    own heap_name (◯ {[ l := (q, to_lock_stateR st, to_agree b) ]}).

  Definition heap_mapsto_mbyte_def (l : loc) (q : Qp) (b: mbyte) : iProp Σ :=
    heap_mapsto_mbyte_st (RSt 0) l q b.
  Definition heap_mapsto_mbyte_aux : seal (@heap_mapsto_mbyte_def). by eexists. Qed.
  Definition heap_mapsto_mbyte := unseal heap_mapsto_mbyte_aux.
  Definition heap_mapsto_mbyte_eq : @heap_mapsto_mbyte = @heap_mapsto_mbyte_def :=
    seal_eq heap_mapsto_mbyte_aux.

  Definition heap_mapsto (l : loc) (q : Qp) (v : val) : iProp Σ :=
    ([∗ list] i ↦ b ∈ v, heap_mapsto_mbyte (l +ₗ i) q b)%I.

  Definition fntbl_entry_def (l : loc) (f: function) : iProp Σ :=
    own heap_fntbl_name (◯ {[ l := to_agree f ]}).
  Definition fntbl_entry_aux : seal (@fntbl_entry_def). by eexists. Qed.
  Definition fntbl_entry := unseal fntbl_entry_aux.
  Definition fntbl_entry_eq : @fntbl_entry = @fntbl_entry_def :=
    seal_eq fntbl_entry_aux.

  Definition heap_ctx (h:heap) : iProp Σ := (own heap_name (● to_heap h))%I.
  Definition fntbl_ctx (t:gmap loc function) : iProp Σ := (own heap_fntbl_name (● to_fntbl t))%I.
  Definition block_used_agree (h:heap) (ub : gset Z) : Prop :=
    ∀ l, l.1 ∉ ub → heap_block_free h l.
  Definition state_ctx (σ:state) : iProp Σ :=
    ⌜block_used_agree σ.(st_heap) σ.(st_used_blocks)⌝
  ∗ heap_ctx σ.(st_heap)
  ∗ fntbl_ctx σ.(st_fntbl).
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
    iDestruct (own_valid_2 with "Htbl Hf") as %[Hf?]%auth_both_valid.
    iPureIntro. move: Hf=> /singleton_included_l [f'].
    rewrite lookup_fmap fmap_Some_equiv => [[[f'' [? ->]]]] /Some_included_total /to_agree_included.
    by intros ->%leibniz_equiv.
  Qed.

End fntbl.

Section block_used_agree.

  Lemma block_used_agree_heap_upd l v v2 f f2 ly h ub:
    heap_at l ly v2 f2 h →
    block_used_agree h ub →
    length v = length v2 → block_used_agree (heap_upd l v f h) ub.
  Proof.
    destruct v, v2 => //. move: ly => -[[|?] ?] [?[?]]// [[?[??]]?].
    move => Hused Hlen l' Hl' o. rewrite heap_upd_lookup_ne. by apply Hused.
    move => Heq. cut (h !! (l +ₗ 0) = None). rewrite shift_loc_0. naive_solver.
    apply Hused. by rewrite Heq.
  Qed.

  Lemma block_used_agree_heap_free_list ls ub h:
    block_used_agree h ub → block_used_agree (heap_free_list ls h) ub.
  Proof. move => Hub l Hl. apply heap_block_free_free_list. by apply Hub. Qed.

  Lemma block_used_agree_heap_upd_list_in ls vs f ub h:
    list_to_set ls.*1 ⊆ ub →
    block_used_agree h ub → block_used_agree (heap_upd_list ls vs f h) ub.
  Proof. move => Hls Hb ??. apply heap_block_free_upd_list; last by set_solver. by apply Hb. Qed.
End block_used_agree.

Section heap.
  Context `{!heapG Σ}.
  Implicit Types P Q : iProp Σ.
  Implicit Types σ : state.
  Implicit Types E : coPset.

  Lemma heap_mapsto_nil l q:
    l ↦{q} [] ⊣⊢ True.
  Proof. by rewrite /heap_mapsto. Qed.

  Lemma heap_mapsto_cons l b v q:
    l ↦{q} (b::v) ⊣⊢ heap_mapsto_mbyte l q b  ∗ (l +ₗ 1) ↦{q} v.
  Proof.
    rewrite /heap_mapsto /= shift_loc_0. setoid_rewrite shift_loc_assoc.
    have Hn:(∀ n, Z.of_nat (S n) = 1 + n) by lia. by setoid_rewrite Hn.
  Qed.

  Lemma heap_mapsto_app l v1 v2 q:
    l ↦{q} (v1 ++ v2) ⊣⊢ l ↦{q} v1 ∗ (l +ₗ length v1) ↦{q} v2.
  Proof.
    elim: v1 l. { move => l. by rewrite /= heap_mapsto_nil left_id shift_loc_0. }
    move => b v1 IH l /=. rewrite !heap_mapsto_cons IH assoc. do 2 f_equiv.
    rewrite shift_loc_assoc. f_equal. lia.
  Qed.

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
  Proof.  rewrite /heap_mapsto. apply _. Qed.

  Global Instance heap_mapsto_fractional l v: Fractional (λ q, l ↦{q} v)%I.
  Proof. rewrite /heap_mapsto. apply _. Qed.

  Global Instance heap_mapsto_as_fractional l q v:
    AsFractional (l ↦{q} v) (λ q, l ↦{q} v)%I q.
  Proof. split. done. apply _. Qed.

  Lemma heap_mapsto_mbyte_agree l q1 q2 v1 v2 : heap_mapsto_mbyte l q1 v1 ∗ heap_mapsto_mbyte l q2 v2 ⊢ ⌜v1 = v2⌝.
  Proof.
    rewrite heap_mapsto_mbyte_eq -own_op -auth_frag_op own_valid discrete_valid.
    eapply pure_elim; [done|]=> /auth_frag_valid /=.
    rewrite singleton_op -pair_op singleton_valid=> -[? /agree_op_invL'->]; eauto.
  Qed.

  Lemma heap_mapsto_agree l q1 q2 v1 v2 :
    length v1 = length v2 →
    l ↦{q1} v1 -∗ l ↦{q2} v2 -∗ ⌜v1 = v2⌝.
  Proof.
    elim: v1 v2 l. by iIntros ([] ??)"??".
    move => ?? IH []//=???[?].
    rewrite !heap_mapsto_cons.
    iIntros "[? ?] [? ?]".
    iDestruct (IH with "[$] [$]") as %-> => //.
    by iDestruct (heap_mapsto_mbyte_agree with "[$]") as %->.
  Qed.

  Lemma heap_alloc l h v :
    heap_block_free h l ->
    heap_ctx h ==∗ heap_ctx (heap_upd l v (λ _, RSt 0%nat) h) ∗ l ↦ v.
  Proof.
    rewrite /heap_block_free => Hfree.
    have [->|Hv] := decide(v = []). 1: iIntros "$ !#"; by rewrite /heap_mapsto.
    rewrite /heap_mapsto heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def.
    rewrite -big_opL_commute1 // -(big_opL_commute auth_frag) -own_op.
    apply own_update, auth_update_alloc.
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
    heap_ctx h ==∗ heap_ctx (heap_upd_list ls vs (λ _, RSt 0%nat) h) ∗ ([∗ list] l;v ∈ ls;vs, l ↦ v).
  Proof.
    elim: ls vs. by move => [] //; iIntros "_ _ _ $ !#".
    move => l ls IH [|v vs] //; csimpl => /Forall_cons[??] /NoDup_cons[??] [?]. iIntros "Hown".
    iMod (IH vs with "Hown") as "[Hown $]" => //.
    iApply (heap_alloc with "Hown").
    by apply heap_block_free_upd_list.
  Qed.

  Lemma heap_mapsto_mbyte_lookup_q ls l h q b:
    heap_ctx h -∗
    heap_mapsto_mbyte_st ls l q b -∗
    ⌜∃ n' : nat,
        h !! l = Some (match ls with RSt n => RSt (n+n') | WSt => WSt end, b)⌝.
  Proof.
    iIntros "H● H◯".
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid.
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
    iDestruct (own_valid_2 with "H● H◯") as %[Hl?]%auth_both_valid.
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
    rewrite heap_mapsto_cons heap_mapsto_mbyte_eq /=. iDestruct "Hl" as "[Hb Hl]".
    iSplit; last by iApply ("IH" with "Hh Hl").
    iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n Hn]. by eauto.
  Qed.

  Lemma heap_mapsto_lookup_1 (flk : lock_state → Prop) l h v:
    flk (RSt 0%nat) →
    heap_ctx h -∗ l ↦ v -∗ ⌜heap_at_go l v flk h⌝.
  Proof.
    iIntros (?) "Hh Hl".
    iInduction v as [|b v] "IH" forall (l) => //.
    rewrite heap_mapsto_cons heap_mapsto_mbyte_eq /=. iDestruct "Hl" as "[Hb Hl]".
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
    rewrite ->heap_mapsto_cons, heap_mapsto_mbyte_eq. iDestruct "Hv" as "[Hb Hl]".
    move: Hat => /= -[[? [Hin [n ?]]] ?]; subst.
    iMod ("IH" with "[] Hh Hl") as "{IH}[Hh IH]" => //.
    iMod (heap_read_mbyte_vs _ 0 1 with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    iModIntro. iSplitL "Hh".
    { iStopProof. f_equiv. symmetry. apply partial_alter_to_insert. by rewrite heap_upd_lookup_lt // Hin. }
    iIntros (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_q with "Hh Hb") as %[n' Hn].
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]".
    iSplitR; first by iPureIntro; naive_solver.
    iMod (heap_read_mbyte_vs _ 1 0 with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    rewrite heap_mapsto_cons heap_mapsto_mbyte_eq. iFrame. iModIntro.
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
    iIntros (Hlen Hf) "Hh Hmt". iInduction (v) as [|v b] "IH" forall (l v' Hlen); destruct v' => //. by iFrame.
    move: Hlen => [] Hlen. rewrite !heap_mapsto_cons !heap_mapsto_mbyte_eq.
    iDestruct "Hmt" as "[Hb Hl]".
    iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as % Hin; auto.
    iMod ("IH" with "[//] Hh Hl") as "[Hh $]".
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh $]". by rewrite heap_upd_lookup_lt.
    iModIntro => /=. iClear "IH". iStopProof. f_equiv => /=. symmetry. apply: partial_alter_to_insert.
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
    rewrite ->heap_mapsto_cons, heap_mapsto_mbyte_eq. iDestruct "Hv" as "[Hb Hl]".
    move: Hat => /= -[[? [Hin ?]] ?]; subst.
    iMod ("IH" with "[] [] Hh Hl") as "{IH}[Hh IH]" => //.
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt.
    iFrame. iIntros "!#" (h2) "Hh". iDestruct (heap_mapsto_mbyte_lookup_1 with "Hh Hb") as %Hn.
    iMod ("IH" with "Hh") as (Hat) "[Hh Hl]".
    iSplitR; first by iPureIntro; naive_solver.
    iMod (heap_write_mbyte_vs with "Hh Hb") as "[Hh Hb]". by rewrite heap_upd_lookup_lt. iFrame.
    rewrite heap_mapsto_cons heap_mapsto_mbyte_eq. by iFrame.
  Qed.


  (* Lemma heap_write v l h v' : *)
  (*   length v = length v' → *)
  (*   heap_ctx h -∗ l ↦ v' ==∗ heap_ctx (heap_upd l v h) ∗ l ↦ v. *)
  (* Proof. *)
  (*   elim: v v' l h. by move => [|??] //= ? l h; iIntros "$ $". *)
  (*   move => b v IH [|b' v'] //= l h [?]. *)
  (*   iIntros "Hctx Hl". *)
  (*   iDestruct (heap_lookup {| ly_size := S (length v')|} with "Hctx Hl") as %[? _] => //. *)
  (*   rewrite heap_mapsto_cons heap_mapsto_mbyte_eq. *)
  (*   iDestruct "Hl" as "[Hb Hmt]". *)
  (*   iMod (IH with "Hctx Hmt") as "[Hctx Hl]" => //. iRevert "Hb". iIntros "Hb". *)
  (*   rewrite heap_mapsto_cons heap_mapsto_mbyte_eq. iFrame. *)
  (*   iStopProof. *)
  (*   rewrite -!own_op to_heap_insert. *)
  (*   apply own_update, auth_update. *)
  (*   eapply (singleton_local_update _ _ (1%Qp, to_agree b') _ (1%Qp, to_agree b)). *)
  (*   - rewrite lookup_fmap heap_upd_lookup_lt //. by simplify_map_eq. *)
  (*   - by apply exclusive_local_update. *)
  (* Qed. *)

  Lemma heap_free_free l ly h :
    heap_ctx h -∗ l ↦|ly| ==∗ heap_ctx (heap_free l ly.(ly_size) h).
  Proof.
    iIntros "Hown". iDestruct 1 as (v <- _) "Hl".
    have [->|Hv] := decide(v = []). done.
    rewrite /heap_mapsto heap_mapsto_mbyte_eq /heap_mapsto_mbyte_def.
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
