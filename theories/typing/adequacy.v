From iris.program_logic Require Export adequacy weakestpre.
From iris.algebra Require Import csum excl auth cmra_big_op gmap.
From refinedc.typing Require Export type.
From refinedc.typing Require Import programs function uninit globals int.
From refinedc.lang Require Import heap.
From iris.program_logic Require Export language.
Set Default Proof Using "Type".

Class typePreG Σ := PreTypeG {
  type_invG :> invPreG Σ;
  type_heap_inG :> inG Σ (authR heapUR);
  type_heap_fntbl_inG :> inG Σ (authR fntblUR);
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR fntblUR))].
Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_prog (main : loc) : stmt :=
  ("res" <- main with []; Return VOID )%E.
Definition initial_thread_state (main : loc) : thread_state := {|
  ts_rfn := {|
    rf_stmt := initial_prog main;
    rf_locs := [];
    rf_fn := {| f_args := []; f_local_vars := []; f_init := ""; f_code := ∅ |}
  |};
  ts_conts := [];
|}.

Definition initial_state (fns : gmap loc function) (gs : gmap loc mbyte) :=
  {| st_heap := (λ b, (RSt 0%nat, b) ) <$> gs;
     st_fntbl := fns;
     st_used_blocks := list_to_set (map_to_list gs).*1.*1 |}.

Lemma wp_to_typed_stmt `{!typeG Σ} (ts : thread_state) v':
  f_code (rf_fn (ts_rfn ts)) = ∅ →
  f_args (rf_fn (ts_rfn ts)) ++ f_local_vars (rf_fn (ts_rfn ts)) = [] →
  to_val (update_stmt ts (Return VOID)) = Some v' →
  typed_stmt ts.(ts_rfn).(rf_stmt) (rf_fn (ts_rfn ts)) [] (λ _ : (), FR (t2mt void) True) ∅ -∗
  WP ts {{ v, True }}.
Proof.
  rewrite /typed_stmt stmt_wp_unfold -{9}(update_stmt_id ts) => ? Happ /of_to_val Hv. iIntros "Hs".
  iApply "Hs" => //. by rewrite Happ. iIntros (v).
  iDestruct 1 as ([]) "[% _]". destruct v => //. rewrite -Hv. by iApply wp_value'.
Qed.

Definition main_type `{!typeG Σ} (P : iProp Σ) :=
    fn(∀ () : (); P) → ∃ () : (), int i32; True.

(** * The main adequacy lemma *)
Lemma refinedc_adequacy Σ `{!typePreG Σ} (thread_mains : list loc) (fns : gmap loc function) (gs : gmap loc mbyte) n t2 σ2 κs:
  (∀ {HtypeG : typeG Σ}, ∃ gl gt,
  let Hglobals : globalG Σ := {| global_locs := gl; global_initialized_types := gt; |} in
      ([∗ map] k↦qs∈gs, k ↦ [qs]) -∗ ([∗ map] k↦qs∈fns, fntbl_entry k qs) ={⊤}=∗
      [∗ list] main ∈ thread_mains, ∃ P, main ◁ᵥ main @ function_ptr (main_type P) ∗ P) →
  nsteps (Λ := stmt_lang) n (initial_thread_state <$> thread_mains, initial_state fns gs ) κs (t2, σ2) →
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => Hwp. apply: wp_strong_adequacy'. move => ?.
  set h := to_heap ((λ b, (RSt 0%nat, b)) <$> gs).
  iMod (own_alloc (Auth (Some (1%Qp, to_agree h)) h)) as (γh) "Hh" => //.
  { apply auth_valid_discrete => /=. split => //. exists h. eauto using to_heap_valid. }
  rewrite (auth_both_op _ h). iDestruct "Hh" as "[Hh Hm]".
  set f := to_fntbl fns.
  iMod (own_alloc (Auth (Some (1%Qp, to_agree f)) f)) as (γf) "Hf" => //.
  { apply auth_valid_discrete => /=. split => //. exists f. eauto using to_fntbl_valid. }
  rewrite (auth_both_op _ f). iDestruct "Hf" as "[Hf Hfm]".

  set (HheapG := HeapG _ _ γh _ γf).
  set (HrefinedCG := RefinedCG _ _ HheapG).
  set (HtypeG := TypeG _ HrefinedCG).
  move: (Hwp HtypeG) => {Hwp} [gl [gt]].
  set (Hglobals := {| global_locs := gl; global_initialized_types := gt; |}).
  move => Hwp.
  iMod (Hwp with "[Hm] [Hfm]") as "Hmains". {
    rewrite /h => {h Hwp}.
    iInduction (gs) as [|?????] "IH" using map_ind => //.
    iApply big_sepM_insert => //. rewrite fmap_insert to_heap_insert.
    rewrite (insert_singleton_op). 2: by apply lookup_to_heap_None; simplify_map_eq.
    iDestruct "Hm" as "[Hx Hm]". rewrite heap_mapsto_cons heap_mapsto_nil heap_mapsto_mbyte_eq. iFrame.
    by iApply "IH".
  } {
    rewrite /f => {f Hwp}.
    iInduction (fns) as [] "IH" using map_ind => //.
    iApply big_sepM_insert => //. rewrite to_fntbl_insert.
    rewrite (insert_singleton_op); last by apply lookup_to_fntbl_None.
    iDestruct "Hfm" as "[Hx Hfm]". rewrite fntbl_entry_eq. iFrame.
    by iApply "IH".
  }

  iModIntro. iExists NotStuck, _, (replicate (length thread_mains) (λ _, True%I)), _.
  iSplitL "Hh Hf"; last first. 1: iSplitL.
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_2. iApply (big_sepL_impl with "Hmains").
    iIntros "!#" (? main ?); iDestruct 1 as (P) "[Hmain HP]".
    iApply wp_to_typed_stmt => //.
    rewrite /= /initial_prog. iApply type_call. iApply type_val. iApply type_val_context.
    iExists (t2mt (main @ function_ptr (main_type P))) => /=. iFrame => /=.
    iApply type_callable. iExists () => /=. iFrame. iIntros (v []) "Hv _" => /=.
    simpl_subst. iApply type_return. iApply type_val. iApply type_void.
    iIntros (_). by iExists ().
  - iFrame. iIntros (?? _ ?) "_ _ _". iApply fupd_mask_weaken => //. iPureIntro. by eauto.
  - iFrame. iPureIntro => /=. clear. move => l Hl i. rewrite lookup_fmap fmap_None.
    destruct (gs !! (l +ₗ i)) as [x|] eqn:? => //. exfalso. apply: Hl.
    apply elem_of_list_to_set. apply elem_of_list_fmap. exists (l +ₗ i). split. by destruct l.
    apply elem_of_list_fmap. eexists (_, x). split => //. apply elem_of_map_to_list. by destruct l.
Qed.

(** * Helper functions for using the adequacy lemma *)
Definition block_to_loc (l: Z): loc := (l, 0%Z).

Definition block_list_to_loc (l: Z): list mbyte → gmap loc mbyte :=
  list_to_map ∘ imap (λ i b, (block_to_loc l +ₗ i, b)).

Lemma block_list_to_loc_nil l :
  block_list_to_loc l [] = ∅.
Proof. done. Qed.

Lemma block_list_to_loc_app l bs x :
  block_list_to_loc l (bs ++ [x]) =
  <[block_to_loc l +ₗ length bs:=x]> (block_list_to_loc l bs).
Proof.
  rewrite /block_list_to_loc /= -list_to_map_cons.
  apply list_to_map_proper; first by apply imap_fst_NoDup, _.
  rewrite imap_app /= -plus_n_O.
    by symmetry; apply Permutation_cons_append.
Qed.

Lemma block_list_to_loc_comm j1 j2 z1 z2 y:
  j1 ≠ j2 →
  block_list_to_loc j1 z1 ∪ (block_list_to_loc j2 z2 ∪ y) =
  block_list_to_loc j2 z2 ∪ (block_list_to_loc j1 z1 ∪ y).
Proof.
  move => Hneq. rewrite !assoc. f_equal. apply map_union_comm.
  apply/map_disjoint_list_to_map_l/Forall_forall => -[??] Hin1.
  apply not_elem_of_list_to_map_1 => /= Hin2. set_solver.
Qed.

Definition heap_list_to_heap : gmap Z (list mbyte) → gmap loc mbyte :=
  map_fold (λ b ls m, block_list_to_loc b ls ∪ m) ∅.

Lemma heap_list_to_heap_insert `{!refinedcG Σ} l v h :
  h !! l = None →
  ([∗ map] k↦qs ∈ heap_list_to_heap (<[l := v]> h), k ↦ [qs]) -∗
  block_to_loc l ↦ v ∗ ([∗ map] k↦qs ∈ heap_list_to_heap h, k ↦ [qs]).
Proof.
  iIntros (HNone) "Hm".
  rewrite /heap_list_to_heap map_fold_insert_L //; last by move => *; apply block_list_to_loc_comm.
  rewrite big_sepM_union.
  - iDestruct "Hm" as "[Hv $]".
    iInduction (v) as [] "IH" using rev_ind. by rewrite heap_mapsto_nil.
    rewrite block_list_to_loc_app heap_mapsto_app big_sepM_insert.
    + iDestruct "Hv" as "[$ Hl]". by iApply "IH".
    + apply not_elem_of_list_to_map_1. set_unfold.
      move => [[??][?[?[?[?/(lookup_lt_Some _ _ _) ?]]]]]. naive_solver lia.
  - apply/map_disjoint_list_to_map_l/Forall_forall => *.
    induction h using map_ind => //.
    move: HNone => /lookup_insert_None [??].
    rewrite map_fold_insert_L //; last by move => *; apply block_list_to_loc_comm.
    apply lookup_union_None. split; last by eauto.
    apply not_elem_of_list_to_map_1. set_solver.
Qed.

Definition fn_lists_to_fns (locs : list loc) (fns : list function) : gmap loc function :=
  list_to_map (zip locs fns).

Lemma fn_lists_to_fns_cons `{!refinedcG Σ} loc fn locs fns :
  length locs = length fns →
  loc ∉ locs →
  ([∗ map] k↦qs ∈ fn_lists_to_fns (loc :: locs) (fn :: fns), fntbl_entry k qs) -∗
  fntbl_entry loc fn ∗ ([∗ map] k↦qs ∈ fn_lists_to_fns locs fns, fntbl_entry k qs).
Proof.
  move => Hnotin ?.
  rewrite /fn_lists_to_fns /= big_sepM_insert //.
  apply not_elem_of_list_to_map_1. rewrite fst_zip => //; lia.
Qed.
