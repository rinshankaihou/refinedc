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
  type_heap_allocs_inG :> inG Σ (authR allocsUR);
  type_heap_fntbl_inG :> inG Σ (authR fntblUR);
}.

Definition typeΣ : gFunctors :=
  #[invΣ;
    GFunctor (constRF (authR heapUR));
    GFunctor (constRF (authR allocsUR));
    GFunctor (constRF (authR fntblUR))].
Instance subG_typePreG {Σ} : subG typeΣ Σ → typePreG Σ.
Proof. solve_inG. Qed.

Definition initial_prog (main : loc) : runtime_expr :=
  coerce_rtexpr (Call main []).

Definition initial_state (fns : gmap loc function) :=
  {| st_heap := ∅;
     st_fntbl := fns;
     st_allocs := ∅; |}.

Definition main_type `{!typeG Σ} (P : iProp Σ) :=
  fn(∀ () : (); P) → ∃ () : (), int i32; True.

(** * The main adequacy lemma *)
Lemma refinedc_adequacy Σ `{!typePreG Σ} (thread_mains : list loc) (fns : gmap loc function) (gls : list loc) (gvs : list lang.val) n t2 σ2 κs σ:
  alloc_new_blocks (initial_state fns) gls gvs σ →
  (∀ {HtypeG : typeG Σ}, ∃ gl gt,
  let Hglobals : globalG Σ := {| global_locs := gl; global_initialized_types := gt; |} in
    ([∗ list] l; v ∈ gls; gvs, l ↦ v) -∗
    ([∗ map] k↦qs∈fns, fntbl_entry k qs) ={⊤}=∗
      [∗ list] main ∈ thread_mains, ∃ P, main ◁ᵥ main @ function_ptr (main_type P) ∗ P) →
  nsteps (Λ := c_lang) n (initial_prog <$> thread_mains, σ) κs (t2, σ2) →
  ∀ e2, e2 ∈ t2 → not_stuck e2 σ2.
Proof.
  move => Hnew Hwp. apply: wp_strong_adequacy. move => ?.
  set h := to_heap ∅.
  iMod (own_alloc (● h ⋅ ◯ h)) as (γh) "[Hh _]" => //.
  { apply auth_both_valid_discrete. split => //. }
  set f := to_fntbl fns.
  iMod (own_alloc (● f ⋅ ◯ f)) as (γf) "[Hf Hfm]" => //.
  { apply auth_both_valid_discrete. split => //. eauto using to_fntbl_valid. }
  set b := to_allocs ∅.
  iMod (own_alloc (● b ⋅ ◯ b)) as (γb) "[Hb _]" => //.
  { apply auth_both_valid_discrete. split => //. }

  set (HheapG := HeapG _ _ γh _ γb _ γf).
  set (HrefinedCG := RefinedCG _ _ HheapG).
  set (HtypeG := TypeG _ HrefinedCG).
  move: (Hwp HtypeG) => {Hwp} [gl [gt]].
  set (Hglobals := {| global_locs := gl; global_initialized_types := gt; |}).
  move => Hwp.
  iMod (heap_alloc_new_blocks_upd with "[Hh Hf Hb]") as "[Hctx Hmt]" => //. { iFrame. }
  iMod (Hwp with "Hmt [Hfm]") as "Hmains". {
    rewrite /f => {f Hwp Hnew}.
    iInduction (fns) as [] "IH" using map_ind => //.
    iApply big_sepM_insert => //. rewrite to_fntbl_insert.
    rewrite (insert_singleton_op); last by apply lookup_to_fntbl_None.
    rewrite fntbl_entry_eq. iDestruct "Hfm" as "[$ Hfm]".
    by iApply "IH".
  }

  iModIntro. iExists NotStuck, _, (replicate (length thread_mains) (λ _, True%I)), _.
  iSplitL "Hctx"; last first. 1: iSplitL.
  - rewrite big_sepL2_fmap_l. iApply big_sepL2_replicate_2. iApply (big_sepL_impl with "Hmains").
    iIntros "!#" (? main ?); iDestruct 1 as (P) "[Hmain HP]".
    iApply (type_call with "[-]"). 2: { by iIntros (??) "??". }
    iApply type_val. iApply type_val_context.
    iExists (t2mt (main @ function_ptr (main_type P))) => /=. iFrame => /=.
    iApply type_callable. iExists () => /=. iFrame. by iIntros (v []) "Hv" => /=.
  - iFrame. iIntros (?? _ _ ?) "_ _ _". iApply fupd_mask_weaken => //. iPureIntro. by eauto.
  - by iFrame.
Qed.

(** * Helper functions for using the adequacy lemma *)
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
