From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.early_alloc Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/early_alloc.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition PAGE_SIZE := (4096).

  Definition PAGES (n : nat) : layout :=
    ly_with_align (n * Z.to_nat PAGE_SIZE) (Z.to_nat PAGE_SIZE).

  Notation PAGE := (PAGES 1).

  (* Definition of type [region]. *)
  Definition region_rec : (loc * nat * nat -d> typeO) → (loc * nat * nat -d> typeO) := (λ self patt__,
    let base := patt__.1.1 in
    let given := patt__.1.2 in
    let remaining := patt__.2 in
    let z_cur : Z := (base.2 + given * PAGE_SIZE)%Z in
    let z_end : Z := (base.2 + (given + remaining) * PAGE_SIZE)%Z in
    struct struct_region [@{type}
      (own_constrained (nonshr_constraint ((base.1, z_cur) ◁ₗ uninit (PAGES remaining))) (value (void*) (base))) ;
      (z_end @ (int (uintptr_t))) ;
      (z_cur @ (int (uintptr_t)))
    ]
  )%I.
  Typeclasses Opaque region_rec.

  Global Instance region_rec_ne : Contractive region_rec.
  Proof. solve_type_proper. Qed.

  Definition region : rtype := {|
    rty_type := loc * nat * nat;
    rty r__ := fixp region_rec r__
  |}.

  Lemma region_unfold (patt__ : loc * nat * nat):
    (patt__ @ region)%I ≡@{type} (
      let base := patt__.1.1 in
      let given := patt__.1.2 in
      let remaining := patt__.2 in
      let z_cur : Z := (base.2 + given * PAGE_SIZE)%Z in
      let z_end : Z := (base.2 + (given + remaining) * PAGE_SIZE)%Z in
      struct struct_region [@{type}
        (own_constrained (nonshr_constraint ((base.1, z_cur) ◁ₗ uninit (PAGES remaining))) (value (void*) (base))) ;
        (z_end @ (int (uintptr_t))) ;
        (z_cur @ (int (uintptr_t)))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance region_rmovable : RMovable region :=
    {| rmovable patt__ := movable_eq _ _ (region_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance region_simplify_hyp_place_inst l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ region)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (region_unfold _)).
  Global Instance region_simplify_goal_place_inst l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ region)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (region_unfold _)).

  Global Program Instance region_simplify_hyp_val_inst v_ patt__:
    SimplifyHypVal v_ (patt__ @ region)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (region_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance region_simplify_goal_val_inst v_ patt__:
    SimplifyGoalVal v_ (patt__ @ region)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (region_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Specifications for function [hyp_early_alloc_nr_pages]. *)
  Definition type_of_hyp_early_alloc_nr_pages :=
    fn(∀ (base, given, remaining) : loc * nat * nat; (global_with_type "mem" Own (((base, given, remaining)) @ (region))))
      → ∃ () : (), (given @ (int (size_t))); (global_with_type "mem" Own (((base, given, remaining)) @ (region))).

  (* Specifications for function [clear_page]. *)
  Definition type_of_clear_page :=
    fn(∀ p : loc; (p @ (&own (uninit (PAGE)))); True)
      → ∃ () : (), (void); (p ◁ₗ (zeroed (PAGE))).

  (* Specifications for function [hyp_early_alloc_contig]. *)
  Definition type_of_hyp_early_alloc_contig :=
    fn(∀ (base, given, remaining, n) : loc * nat * nat * nat; (n @ (int (u32))); (global_with_type "mem" Own (((base, given, remaining)) @ (region))))
      → ∃ () : (), ((0%nat < n ≤ remaining) @ (optional (&own (uninit (PAGES (n)))) null)); (global_with_type "mem" Own ((if bool_decide (0%nat < n ≤ remaining) then (base, given + n, remaining - n)%nat else (base, given, remaining)) @ (region))).

  (* Specifications for function [hyp_early_alloc_page]. *)
  Definition type_of_hyp_early_alloc_page :=
    fn(∀ (base, given, remaining) : loc * nat * nat; (uninit (void*)); (global_with_type "mem" Own (((base, given, remaining)) @ (region))))
      → ∃ () : (), ((remaining ≠ 0%nat) @ (optional (&own (uninit (PAGE))) null)); (global_with_type "mem" Own ((if bool_decide (remaining ≠ 0%nat) then (base, given + 1, remaining - 1)%nat else (base, given, remaining)) @ (region))).

  (* Specifications for function [hyp_early_alloc_init]. *)
  Definition type_of_hyp_early_alloc_init :=
    fn(∀ (l, n, s) : loc * nat * Z; (l @ (&own (uninit (PAGES (n))))), (s @ (int (u32))); ⌜s = (n * PAGE_SIZE)%Z⌝ ∗ (global_with_type "mem" Own (uninit (struct_region))))
      → ∃ () : (), (void); (global_with_type "mem" Own (((l, 0%nat, n)) @ (region))).
End spec.

Typeclasses Opaque region_rec.
