From refinedc.typing Require Import typing.
From refinedc.linux.casestudies.page_alloc Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
From caesium Require Import builtins_specs.
From refinedc.linux.casestudies.page_alloc Require Import page_alloc_def.
Set Default Proof Using "Type".

(* Generated from [linux/casestudies/page_alloc.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition HYP_MAX_ORDER : nat := Z.to_nat 11.
  Definition HYP_NO_ORDER : Z := max_int u32.

  (* Definition of type [hyp_page]. *)
  Definition hyp_page_rec : (loc * loc * nat * Z * Z * (option (option Z)) → type) → (loc * loc * nat * Z * Z * (option (option Z)) → type) := (λ self patt__,
    let pool := patt__.1.1.1.1.1 in
    let vmemmap := patt__.1.1.1.1.2 in
    let vmemmap_len := patt__.1.1.1.2 in
    let refcount := patt__.1.1.2 in
    let order := patt__.1.2 in
    let next := patt__.2 in
    (immovable (λ self,
      struct struct_hyp_page [@{type}
        (refcount @ (int (u32))) ;
        (order @ (int (u32))) ;
        (&own (place (pool))) ;
        (own_constrained (nonshr_constraint (hyp_page_to_virt vmemmap self ◁ₗ next @ optionalO (λ _, uninit (PAGE_LAYOUT (Z.shiftl 1 order))) (place (hyp_page_to_virt vmemmap self)))) (list_node (idx_to_node (vmemmap) (vmemmap_len) (next))))
      ]
    ))
  )%I.
  Global Typeclasses Opaque hyp_page_rec.

  Global Instance hyp_page_rec_le : TypeMono hyp_page_rec.
  Proof. solve_type_proper. Qed.

  Definition hyp_page : rtype (loc * loc * nat * Z * Z * (option (option Z))) := {|
    rty r__ := hyp_page_rec (type_fixpoint hyp_page_rec) r__
  |}.

  Lemma hyp_page_unfold (patt__ : loc * loc * nat * Z * Z * (option (option Z))):
    (patt__ @ hyp_page)%I ≡@{type} (
      let pool := patt__.1.1.1.1.1 in
      let vmemmap := patt__.1.1.1.1.2 in
      let vmemmap_len := patt__.1.1.1.2 in
      let refcount := patt__.1.1.2 in
      let order := patt__.1.2 in
      let next := patt__.2 in
      (immovable (λ self,
        struct struct_hyp_page [@{type}
          (refcount @ (int (u32))) ;
          (order @ (int (u32))) ;
          (&own (place (pool))) ;
          (own_constrained (nonshr_constraint (hyp_page_to_virt vmemmap self ◁ₗ next @ optionalO (λ _, uninit (PAGE_LAYOUT (Z.shiftl 1 order))) (place (hyp_page_to_virt vmemmap self)))) (list_node (idx_to_node (vmemmap) (vmemmap_len) (next))))
        ]
      ))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 hyp_page_rec). Qed.

  Definition hyp_page_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_hyp_place_inst_generated.
  Definition hyp_page_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (hyp_page_unfold patt__) with 100%N].
  Global Existing Instance hyp_page_simplify_goal_place_inst_generated.

  (* Definition of type [hyp_pool]. *)
  Definition hyp_pool_rec : ((list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * loc * Z * Z → type) → ((list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * loc * Z * Z → type) := (λ self patt__,
    let heads := patt__.1.1.1.1.1 in
    let pages := patt__.1.1.1.1.2 in
    let npages := patt__.1.1.1.2 in
    let vmemmap := patt__.1.1.2 in
    let range_start := patt__.1.2 in
    let range_end := patt__.2 in
    (immovable (λ self,
      ∃ₜ (lid : lock_id),
      constrained (struct struct_hyp_pool [@{type}
        (own_constrained (nonshr_constraint (vmemmap ◁ₗ  (array (struct_hyp_page) (((λ '(ref_count, order, next), (self, vmemmap, npages, ref_count, order, next)) <$> pages) `at_type` hyp_page))  )) (spinlock (lid))) ;
        (array (struct_list_head) ((λ h,  (list_node (idx_to_node (vmemmap) (npages) (h))) ) <$> heads)) ;
        (range_start @ (int (u64))) ;
        (range_end @ (int (u64)))
      ]) (
        (initialized "__hyp_vmemmap" vmemmap) ∗
        ⌜length pages = npages⌝
      )
    ))
  )%I.
  Global Typeclasses Opaque hyp_pool_rec.

  Global Instance hyp_pool_rec_le : TypeMono hyp_pool_rec.
  Proof. solve_type_proper. Qed.

  Definition hyp_pool : rtype ((list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * loc * Z * Z) := {|
    rty r__ := hyp_pool_rec (type_fixpoint hyp_pool_rec) r__
  |}.

  Lemma hyp_pool_unfold (patt__ : (list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * loc * Z * Z):
    (patt__ @ hyp_pool)%I ≡@{type} (
      let heads := patt__.1.1.1.1.1 in
      let pages := patt__.1.1.1.1.2 in
      let npages := patt__.1.1.1.2 in
      let vmemmap := patt__.1.1.2 in
      let range_start := patt__.1.2 in
      let range_end := patt__.2 in
      (immovable (λ self,
        ∃ₜ (lid : lock_id),
        constrained (struct struct_hyp_pool [@{type}
          (own_constrained (nonshr_constraint (vmemmap ◁ₗ  (array (struct_hyp_page) (((λ '(ref_count, order, next), (self, vmemmap, npages, ref_count, order, next)) <$> pages) `at_type` hyp_page))  )) (spinlock (lid))) ;
          (array (struct_list_head) ((λ h,  (list_node (idx_to_node (vmemmap) (npages) (h))) ) <$> heads)) ;
          (range_start @ (int (u64))) ;
          (range_end @ (int (u64)))
        ]) (
          (initialized "__hyp_vmemmap" vmemmap) ∗
          ⌜length pages = npages⌝
        )
      ))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 hyp_pool_rec). Qed.

  Definition hyp_pool_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_hyp_place_inst_generated.
  Definition hyp_pool_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (hyp_pool_unfold patt__) with 100%N].
  Global Existing Instance hyp_pool_simplify_goal_place_inst_generated.

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [sl_init]. *)
  Definition type_of_sl_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_spinlock)))); True)
      → ∃ gamma : lock_id, (void); (p ◁ₗ (spinlock (gamma))).

  (* Specifications for function [sl_lock]. *)
  Definition type_of_sl_lock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (lock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (lock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [sl_lock_both]. *)
  Definition type_of_sl_lock_both :=
    fn(∀ (p2, gamma2, beta2, p1, gamma1, beta1) : loc * lock_id * own_state * loc * lock_id * own_state; (p2 @ (&frac{beta2} (spinlock (gamma2)))), (p1 @ (&frac{beta1} (spinlock (gamma1)))); True)
      → ∃ () : (), (void); (p2 ◁ₗ{beta2} (spinlock (gamma2))) ∗ (lock_token gamma2 []) ∗ (p1 ◁ₗ{beta1} (spinlock (gamma1))) ∗ (lock_token gamma1 []).

  (* Specifications for function [sl_lock_both_same_prov]. *)
  Definition type_of_sl_lock_both_same_prov :=
    fn(∀ (p2, gamma2, beta2, p1, gamma1, beta1) : loc * lock_id * own_state * loc * lock_id * own_state; (p2 @ (&frac{beta2} (spinlock (gamma2)))), (p1 @ (&frac{beta1} (spinlock (gamma1)))); ⌜p1.1 = p2.1⌝)
      → ∃ () : (), (void); (p2 ◁ₗ{beta2} (spinlock (gamma2))) ∗ (lock_token gamma2 []) ∗ (p1 ◁ₗ{beta1} (spinlock (gamma1))) ∗ (lock_token gamma1 []).

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [clear_page]. *)
  Definition type_of_clear_page :=
    fn(∀ p : loc; (p @ (&own (uninit (PAGE_LAYOUT (1))))); True)
      → ∃ () : (), (void); (p ◁ₗ (zeroed (PAGE_LAYOUT (1)))).

  (* Function [memset] has been skipped. *)

  (* Function [hyp_panic] has been skipped. *)

  (* Function [__list_add_valid] has been skipped. *)

  (* Function [__list_del_entry_valid] has been skipped. *)

  (* Function [INIT_LIST_HEAD] has been skipped. *)

  (* Function [__list_add] has been skipped. *)

  (* Specifications for function [list_add]. *)
  Definition type_of_list_add :=
    fn(∀ (pnew, phead, next) : loc * loc * (option (option type)); (pnew @ (&own (list_node (None)))), (phead @ (&own (list_node (next)))); True)
      → ∃ () : (), (void); (pnew ◁ₗ (list_node (next))) ∗ (phead ◁ₗ (list_node (Some (Some (place pnew))))).

  (* Function [list_add_tail] has been skipped. *)

  (* Function [__list_del] has been skipped. *)

  (* Function [__list_del_entry] has been skipped. *)

  (* Specifications for function [list_del_init]. *)
  Definition type_of_list_del_init :=
    fn(∀ (p, next) : loc * (option (option type)); (p @ (&own (list_node (next)))); True)
      → ∃ () : (), (void); (p ◁ₗ (list_node (None))).

  (* Specifications for function [list_empty]. *)
  Definition type_of_list_empty :=
    fn(∀ (p, next) : loc * (option (option type)); (p @ (&own (list_node (next)))); True)
      → ∃ () : (), ((bool_decide (next = None)) @ (boolean (i32))); (p ◁ₗ (list_node (next))).

  (* Function [hyp_phys_to_virt] has been skipped. *)

  (* Function [hyp_virt_to_phys] has been skipped. *)

  (* Specifications for function [hyp_phys_to_page]. *)
  Definition type_of_hyp_phys_to_page :=
    fn(∀ (p, vmemmap, pages) : Z * loc * (list type); (p @ (int (u64))); (initialized "__hyp_vmemmap" vmemmap) ∗ (vmemmap ◁ₗ (array (struct_hyp_page) (pages))))
      → ∃ () : (), (&own (array_ptr (struct_hyp_page) (vmemmap) (hyp_phys_to_page vmemmap p) (length pages))); (vmemmap ◁ₗ (array (struct_hyp_page) (pages))).

  (* Specifications for function [hyp_page_to_phys]. *)
  Definition type_of_hyp_page_to_phys :=
    fn(∀ (p, page, vmemmap, len) : loc * Z * loc * nat; (p @ (&own (array_ptr (struct_hyp_page) (vmemmap) (page) (len)))); (initialized "__hyp_vmemmap" vmemmap))
      → ∃ () : (), ((hyp_page_to_phys vmemmap page) @ (int (u64))); (p ◁ₗ (array_ptr (struct_hyp_page) (vmemmap) (page) (len))).

  (* Function [hyp_page_count] has been skipped. *)

  (* Function [hyp_alloc_pages] has been skipped. *)

  (* Function [hyp_get_page] has been skipped. *)

  (* Function [hyp_put_page] has been skipped. *)

  (* Function [hyp_pool_init] has been skipped. *)

  (* Specifications for function [__find_buddy]. *)
  Definition type_of___find_buddy :=
    fn(∀ (pool, pageloc, page, vmemmap, heads, pages, npages, range_start, range_end, order) : loc * loc * Z * loc * (list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * Z * Z * Z; (pool @ (&own (((heads, pages, npages, vmemmap, range_start, range_end)) @ (hyp_pool)))), (pageloc @ (&own (array_ptr (struct_hyp_page) (vmemmap) (page) (npages)))), (order @ (int (u32))); True)
      → ∃ () : (), ((0 <= find_buddy vmemmap order page < npages) @ (optional (&own (array_ptr (struct_hyp_page) (vmemmap) (find_buddy vmemmap order page) (npages))) (null))); (pool ◁ₗ (((heads, pages, npages, vmemmap, range_start, range_end)) @ (hyp_pool))) ∗ (pageloc ◁ₗ (array_ptr (struct_hyp_page) (vmemmap) (page) (npages))).

  (* Specifications for function [__hyp_attach_page]. *)
  Definition type_of___hyp_attach_page :=
    fn(∀ (pool, page, vmemmap, heads, pages, npages, range_start, range_end, order) : loc * Z * loc * (list (option (option Z))) * (list (Z * Z * (option (option Z)))) * nat * Z * Z * Z; (pool @ (&own (((heads, pages, npages, vmemmap, range_start, range_end)) @ (hyp_pool)))), (&own (array_ptr (struct_hyp_page) (vmemmap) (page) (npages))); ⌜0 <= page < npages⌝ ∗ ⌜pages !! Z.to_nat page = Some (0, order, None)⌝ ∗ (hyp_page_to_virt vmemmap (vmemmap offset{struct_hyp_page}ₗ page) ◁ₗ uninit (PAGE_LAYOUT (1 ≪ order))))
      → ∃ (heads2, pages2) : _ * _, (void); (pool ◁ₗ (((heads2, pages2, npages, vmemmap, range_start, range_end)) @ (hyp_pool))).

  (* Function [__hyp_extract_page] has been skipped. *)

  (* Function [clear_hyp_page] has been skipped. *)

  (* Function [__hyp_alloc_pages] has been skipped. *)
End spec.

Global Typeclasses Opaque hyp_page_rec.
Global Typeclasses Opaque hyp_page.
Global Typeclasses Opaque hyp_pool_rec.
Global Typeclasses Opaque hyp_pool.
