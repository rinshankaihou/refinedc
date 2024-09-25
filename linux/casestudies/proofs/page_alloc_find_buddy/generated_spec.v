From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.linux.casestudies.page_alloc_find_buddy Require Import page_alloc_def.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc_find_buddy.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition HYP_MAX_ORDER : nat := Z.to_nat 11.
  Definition HYP_NO_ORDER : Z := max_int u32.

  (* Definition of type [hyp_page]. *)
  Definition hyp_page_rec : (Z * Z → type) → (Z * Z → type) := (λ self patt__,
    let refcount := patt__.1 in
    let order := patt__.2 in
    struct struct_hyp_page [@{type}
      (refcount @ (int (u16))) ;
      (order @ (int (u16)))
    ]
  )%I.
  Global Typeclasses Opaque hyp_page_rec.

  Global Instance hyp_page_rec_le : TypeMono hyp_page_rec.
  Proof. solve_type_proper. Qed.

  Definition hyp_page : rtype (Z * Z) := {|
    rty r__ := hyp_page_rec (type_fixpoint hyp_page_rec) r__
  |}.

  Lemma hyp_page_unfold (patt__ : Z * Z):
    (patt__ @ hyp_page)%I ≡@{type} (
      let refcount := patt__.1 in
      let order := patt__.2 in
      struct struct_hyp_page [@{type}
        (refcount @ (int (u16))) ;
        (order @ (int (u16)))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 hyp_page_rec). Qed.

  Definition hyp_page_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_hyp_place_inst_generated.
  Definition hyp_page_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_goal_place_inst_generated.

  Definition hyp_page_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_hyp_val_inst_generated.
  Definition hyp_page_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_goal_val_inst_generated.

  (* Definition of type [hyp_pool]. *)
  Definition hyp_pool_rec : ((list (Z * Z)) * nat * loc * Z * Z → type) → ((list (Z * Z)) * nat * loc * Z * Z → type) := (λ self patt__,
    let pages := patt__.1.1.1.1 in
    let npages := patt__.1.1.1.2 in
    let vmemmap := patt__.1.1.2 in
    let range_start_idx := patt__.1.2 in
    let max_order := patt__.2 in
    ∃ₜ (range_start : Z) (range_end : Z),
    constrained (struct struct_hyp_pool [@{type}
      (own_constrained (nonshr_constraint (vmemmap ◁ₗ  (array (struct_hyp_page) (pages `at_type` hyp_page))  )) (range_start @ (int (u64)))) ;
      (range_end @ (int (u64))) ;
      (max_order @ (int (u16)))
    ]) (
      (initialized "__hyp_vmemmap" vmemmap) ∗
      ⌜(length pages =@{Z} range_start_idx + npages)%Z⌝ ∗
      ⌜(range_start = range_start_idx ≪ PAGE_SHIFT)%Z⌝ ∗
      ⌜(range_end = range_start + npages ≪ PAGE_SHIFT)%Z⌝ ∗
      ⌜(0 <= range_start_idx)%Z⌝
    )
  )%I.
  Global Typeclasses Opaque hyp_pool_rec.

  Global Instance hyp_pool_rec_le : TypeMono hyp_pool_rec.
  Proof. solve_type_proper. Qed.

  Definition hyp_pool : rtype ((list (Z * Z)) * nat * loc * Z * Z) := {|
    rty r__ := hyp_pool_rec (type_fixpoint hyp_pool_rec) r__
  |}.

  Lemma hyp_pool_unfold (patt__ : (list (Z * Z)) * nat * loc * Z * Z):
    (patt__ @ hyp_pool)%I ≡@{type} (
      let pages := patt__.1.1.1.1 in
      let npages := patt__.1.1.1.2 in
      let vmemmap := patt__.1.1.2 in
      let range_start_idx := patt__.1.2 in
      let max_order := patt__.2 in
      ∃ₜ (range_start : Z) (range_end : Z),
      constrained (struct struct_hyp_pool [@{type}
        (own_constrained (nonshr_constraint (vmemmap ◁ₗ  (array (struct_hyp_page) (pages `at_type` hyp_page))  )) (range_start @ (int (u64)))) ;
        (range_end @ (int (u64))) ;
        (max_order @ (int (u16)))
      ]) (
        (initialized "__hyp_vmemmap" vmemmap) ∗
        ⌜(length pages =@{Z} range_start_idx + npages)%Z⌝ ∗
        ⌜(range_start = range_start_idx ≪ PAGE_SHIFT)%Z⌝ ∗
        ⌜(range_end = range_start + npages ≪ PAGE_SHIFT)%Z⌝ ∗
        ⌜(0 <= range_start_idx)%Z⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 hyp_pool_rec). Qed.

  Definition hyp_pool_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_hyp_place_inst_generated.
  Definition hyp_pool_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_goal_place_inst_generated.

  Definition hyp_pool_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_hyp_val_inst_generated.
  Definition hyp_pool_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Function [hyp_phys_to_virt] has been skipped. *)

  (* Function [hyp_virt_to_phys] has been skipped. *)

  (* Function [hyp_alloc_pages] has been skipped. *)

  (* Function [hyp_get_page] has been skipped. *)

  (* Function [hyp_put_page] has been skipped. *)

  (* Function [hyp_pool_init] has been skipped. *)

  (* Specifications for function [__find_buddy]. *)
  Definition type_of___find_buddy :=
    fn(∀ (pool, pageloc, page, vmemmap, pages, npages, range_start_idx, order, max_order) : loc * loc * Z * loc * (list (Z * Z)) * nat * Z * Z * Z; (pool @ (&own (((pages, npages, vmemmap, range_start_idx, max_order)) @ (hyp_pool)))), (pageloc @ (&own (array_ptr (struct_hyp_page) (vmemmap) (page) (length pages)))), (order @ (int (u32))); ⌜0 <= page ≪ 12 <= max_int ptrdiff_t⌝ ∗ ⌜0 < length pages⌝ ∗ ⌜0 <= order <= HYP_MAX_ORDER⌝)
      → ∃ () : (), ((range_start_idx <= find_buddy vmemmap order page < range_start_idx + npages) @ (optional (&own (array_ptr (struct_hyp_page) (vmemmap) (find_buddy vmemmap order page) (length pages))) (null))); (pool ◁ₗ (((pages, npages, vmemmap, range_start_idx, max_order)) @ (hyp_pool))) ∗ (pageloc ◁ₗ (array_ptr (struct_hyp_page) (vmemmap) (page) (length pages))).
End spec.

Global Typeclasses Opaque hyp_page_rec.
Global Typeclasses Opaque hyp_page.
Global Typeclasses Opaque hyp_pool_rec.
Global Typeclasses Opaque hyp_pool.
