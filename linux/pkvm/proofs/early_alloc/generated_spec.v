From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)

(* Inlined code (prelude). *)

Notation PAGE_SHIFT := (12).
Notation PAGE_SIZE := (4096).

Definition PAGES (n : nat) : layout :=
  ly_with_align (n * Z.to_nat PAGE_SIZE) (Z.to_nat PAGE_SIZE).

Notation PAGE := (PAGES 1).

Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [region]. *)
  Definition region_rec : (loc * Z * Z → type) → (loc * Z * Z → type) := (λ self patt__,
    let base := patt__.1.1 in
    let given := patt__.1.2 in
    let remaining := patt__.2 in
    let z_cur : Z := (base.2 + given * PAGE_SIZE)%Z in
    let z_end : Z := (base.2 + (given + remaining) * PAGE_SIZE)%Z in
    constrained (struct struct_region [@{type}
      (z_end @ (int (u64))) ;
      (z_cur @ (int (u64))) ;
      (own_constrained (nonshr_constraint ((base.1, z_cur) ◁ₗ uninit (PAGES (Z.to_nat remaining)))) (base @ (intptr (u64))))
    ]) (
      ⌜0 ≤ given⌝ ∗
      ⌜0 ≤ remaining⌝ ∗
      (alloc_global base) ∗
      ⌜base.2 + (given + remaining) * PAGE_SIZE ≤ max_int u64⌝
    )
  )%I.
  Global Typeclasses Opaque region_rec.

  Global Instance region_rec_le : TypeMono region_rec.
  Proof. solve_type_proper. Qed.

  Definition region : rtype (loc * Z * Z) := {|
    rty r__ := region_rec (type_fixpoint region_rec) r__
  |}.

  Lemma region_unfold (patt__ : loc * Z * Z):
    (patt__ @ region)%I ≡@{type} (
      let base := patt__.1.1 in
      let given := patt__.1.2 in
      let remaining := patt__.2 in
      let z_cur : Z := (base.2 + given * PAGE_SIZE)%Z in
      let z_end : Z := (base.2 + (given + remaining) * PAGE_SIZE)%Z in
      constrained (struct struct_region [@{type}
        (z_end @ (int (u64))) ;
        (z_cur @ (int (u64))) ;
        (own_constrained (nonshr_constraint ((base.1, z_cur) ◁ₗ uninit (PAGES (Z.to_nat remaining)))) (base @ (intptr (u64))))
      ]) (
        ⌜0 ≤ given⌝ ∗
        ⌜0 ≤ remaining⌝ ∗
        (alloc_global base) ∗
        ⌜base.2 + (given + remaining) * PAGE_SIZE ≤ max_int u64⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 region_rec). Qed.

  Definition region_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (region_unfold patt__) with 100%N].
  Global Existing Instance region_simplify_hyp_place_inst_generated.
  Definition region_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (region_unfold patt__) with 100%N].
  Global Existing Instance region_simplify_goal_place_inst_generated.

  Definition region_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (region_unfold patt__) with 100%N].
  Global Existing Instance region_simplify_hyp_val_inst_generated.
  Definition region_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (region_unfold patt__) with 100%N].
  Global Existing Instance region_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [memset]. *)
  Definition type_of_memset :=
    fn(∀ (p, n) : loc * Z; (&own (place (p))), ((0) @ (int (u8))), (n @ (int (u64))); (p ◁ₗ (uninit (ly_with_align (Z.to_nat n) (Z.to_nat PAGE_SIZE)))))
      → ∃ () : (), (void); (p ◁ₗ (zeroed (ly_with_align (Z.to_nat n) (Z.to_nat PAGE_SIZE)))).

  (* Specifications for function [hyp_early_alloc_nr_used_pages]. *)
  Definition type_of_hyp_early_alloc_nr_used_pages :=
    fn(∀ (base, given, remaining) : loc * Z * Z; (global_with_type "mem" Own (((base, given, remaining)) @ (region))))
      → ∃ () : (), (given @ (int (size_t))); (global_with_type "mem" Own (((base, given, remaining)) @ (region))).

  (* Specifications for function [hyp_early_alloc_contig]. *)
  Definition type_of_hyp_early_alloc_contig :=
    fn(∀ (base, given, remaining, n) : loc * Z * Z * Z; (n @ (int (u32))); (global_with_type "mem" Own (((base, given, remaining)) @ (region))) ∗ ⌜0 < n ≤ remaining⌝ ∗ ⌜n ≪ PAGE_SHIFT ≤ max_int u32⌝)
      → ∃ () : (), (&own (zeroed (PAGES (Z.to_nat n)))); (global_with_type "mem" Own (((base, given + n, remaining - n)%Z) @ (region))).

  (* Specifications for function [hyp_early_alloc_page]. *)
  Definition type_of_hyp_early_alloc_page :=
    fn(∀ (base, given, remaining) : loc * Z * Z; (uninit (void*)); (global_with_type "mem" Own (((base, given, remaining)) @ (region))) ∗ ⌜0 < remaining⌝)
      → ∃ () : (), (&own (zeroed (PAGE))); (global_with_type "mem" Own (((base, given + 1, remaining - 1)) @ (region))).

  (* Specifications for function [hyp_early_alloc_init]. *)
  Definition type_of_hyp_early_alloc_init :=
    fn(∀ (l, n, s) : loc * Z * Z; (l @ (&own (uninit (PAGES (Z.to_nat n))))), (s @ (int (u64))); ⌜s = (n * PAGE_SIZE)%Z⌝ ∗ (alloc_global l) ∗ (global_with_type "mem" Own (uninit (struct_region))))
      → ∃ () : (), (void); (global_with_type "mem" Own (((l, 0, n)) @ (region))).
End spec.

Global Typeclasses Opaque region_rec.
Global Typeclasses Opaque region.
