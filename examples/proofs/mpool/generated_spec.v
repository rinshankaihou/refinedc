From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Definition of type [mpool_chunk_t]. *)
  Definition mpool_chunk_t_rec : (nat * nat -d> typeO) → (nat * nat -d> typeO) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      tyexists (λ local : nat,
      tyexists (λ next : nat,
      tyexists (λ ly : layout,
      constrained (padded (struct struct_mpool_chunk [@{type}
        ((local * entry_size) @ (int (size_t))) ;
        (guarded ("mpool_chunk_t_0") (apply_dfun self (next, (entry_size))))
      ]) struct_mpool_chunk ly) (
        ⌜(len = local + next)%nat⌝ ∗
        ⌜local > 0⌝ ∗
        ⌜ly = ly_with_align (local * entry_size) entry_size⌝
      ))))
    )) null))
  )%I.
  Typeclasses Opaque mpool_chunk_t_rec.

  Global Instance mpool_chunk_t_rec_ne : Contractive mpool_chunk_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_chunk_t (entry_size : nat) : rtype := {|
    rty_type := nat;
    rty r__ := fixp mpool_chunk_t_rec (r__, entry_size)
  |}.

  Lemma mpool_chunk_t_unfold (entry_size : nat) (len : nat) :
    (len @ mpool_chunk_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        tyexists (λ local : nat,
        tyexists (λ next : nat,
        tyexists (λ ly : layout,
        constrained (padded (struct struct_mpool_chunk [@{type}
          ((local * entry_size) @ (int (size_t))) ;
          (guarded "mpool_chunk_t_0" (next @ (mpool_chunk_t (entry_size))))
        ]) struct_mpool_chunk ly) (
          ⌜(len = local + next)%nat⌝ ∗
          ⌜local > 0⌝ ∗
          ⌜ly = ly_with_align (local * entry_size) entry_size⌝
        ))))
      )) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mpool_chunk_t_rmovable (entry_size : nat) : RMovable (mpool_chunk_t entry_size) :=
    {| rmovable 'len := movable_eq _ _ (mpool_chunk_t_unfold entry_size len) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mpool_chunk_t_simplify_hyp_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyHypPlace l_ β_ (len @ mpool_chunk_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mpool_chunk_t_unfold _ _)).
  Global Instance mpool_chunk_t_simplify_goal_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyGoalPlace l_ β_ (len @ mpool_chunk_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mpool_chunk_t_unfold _ _)).

  Global Program Instance mpool_chunk_t_simplify_hyp_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyHypVal v_ (len @ mpool_chunk_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mpool_chunk_t_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mpool_chunk_t_simplify_goal_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyGoalVal v_ (len @ mpool_chunk_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mpool_chunk_t_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [mpool_entry_t]. *)
  Definition mpool_entry_t_rec : (nat * nat -d> typeO) → (nat * nat -d> typeO) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      padded (struct struct_mpool_entry [@{type}
        (guarded ("mpool_entry_t_0") (apply_dfun self (((len - 1)%nat), (entry_size))))
      ]) struct_mpool_entry (ly_with_align entry_size entry_size)
    )) null))
  )%I.
  Typeclasses Opaque mpool_entry_t_rec.

  Global Instance mpool_entry_t_rec_ne : Contractive mpool_entry_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_entry_t (entry_size : nat) : rtype := {|
    rty_type := nat;
    rty r__ := fixp mpool_entry_t_rec (r__, entry_size)
  |}.

  Lemma mpool_entry_t_unfold (entry_size : nat) (len : nat) :
    (len @ mpool_entry_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        padded (struct struct_mpool_entry [@{type}
          (guarded "mpool_entry_t_0" (((len - 1)%nat) @ (mpool_entry_t (entry_size))))
        ]) struct_mpool_entry (ly_with_align entry_size entry_size)
      )) null))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mpool_entry_t_rmovable (entry_size : nat) : RMovable (mpool_entry_t entry_size) :=
    {| rmovable 'len := movable_eq _ _ (mpool_entry_t_unfold entry_size len) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mpool_entry_t_simplify_hyp_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyHypPlace l_ β_ (len @ mpool_entry_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mpool_entry_t_unfold _ _)).
  Global Instance mpool_entry_t_simplify_goal_place_inst l_ β_ (entry_size : nat) (len : nat) :
    SimplifyGoalPlace l_ β_ (len @ mpool_entry_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mpool_entry_t_unfold _ _)).

  Global Program Instance mpool_entry_t_simplify_hyp_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyHypVal v_ (len @ mpool_entry_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mpool_entry_t_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mpool_entry_t_simplify_goal_val_inst v_ (entry_size : nat) (len : nat) :
    SimplifyGoalVal v_ (len @ mpool_entry_t entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mpool_entry_t_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [mpool]. *)
  Definition mpool_rec : (nat * nat -d> typeO) → (nat * nat -d> typeO) := (λ self patt__,
    let entries := patt__.1 in
    let entry_size := patt__.2 in
    tyexists (λ lid : lock_id,
    constrained (struct struct_mpool [@{type}
      (entry_size @ (int (size_t))) ;
      (spinlock (lid)) ;
      ((spinlocked_ex (lid) ("locked") (entries) (λ entries,
        tyexists (λ entries_in_chunks : nat,
        tyexists (λ entries_in_entry_list : nat,
        constrained (struct struct_mpool_locked_inner [@{type}
          (entries_in_chunks @ (mpool_chunk_t (entry_size))) ;
          (entries_in_entry_list @ (mpool_entry_t (entry_size)))
        ]) (
          ⌜(entries = entries_in_chunks + entries_in_entry_list)%nat⌝
        )))
      ))) ;
      (optionalO (λ _ : unit,
        &shr (tyexists (λ n, guarded ("mpool_0") (apply_dfun self (n, (entry_size)))))
      ) null)
    ]) (
      ⌜is_power_of_two entry_size⌝ ∗
      ⌜layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size⌝ ∗
      ⌜layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size⌝
    ))
  )%I.
  Typeclasses Opaque mpool_rec.

  Global Instance mpool_rec_ne : Contractive mpool_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool (entry_size : nat) : rtype := {|
    rty_type := nat;
    rty r__ := fixp mpool_rec (r__, entry_size)
  |}.

  Lemma mpool_unfold (entry_size : nat) (entries : nat) :
    (entries @ mpool entry_size)%I ≡@{type} (
      tyexists (λ lid : lock_id,
      constrained (struct struct_mpool [@{type}
        (entry_size @ (int (size_t))) ;
        (spinlock (lid)) ;
        ((spinlocked_ex (lid) ("locked") (entries) (λ entries,
          tyexists (λ entries_in_chunks : nat,
          tyexists (λ entries_in_entry_list : nat,
          constrained (struct struct_mpool_locked_inner [@{type}
            (entries_in_chunks @ (mpool_chunk_t (entry_size))) ;
            (entries_in_entry_list @ (mpool_entry_t (entry_size)))
          ]) (
            ⌜(entries = entries_in_chunks + entries_in_entry_list)%nat⌝
          )))
        ))) ;
        (optionalO (λ _ : unit,
          &shr (tyexists (λ n, guarded "mpool_0" (n @ (mpool (entry_size)))))
        ) null)
      ]) (
        ⌜is_power_of_two entry_size⌝ ∗
        ⌜layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size⌝ ∗
        ⌜layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size⌝
      ))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mpool_rmovable (entry_size : nat) : RMovable (mpool entry_size) :=
    {| rmovable 'entries := movable_eq _ _ (mpool_unfold entry_size entries) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mpool_simplify_hyp_place_inst l_ β_ (entry_size : nat) (entries : nat) :
    SimplifyHypPlace l_ β_ (entries @ mpool entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mpool_unfold _ _)).
  Global Instance mpool_simplify_goal_place_inst l_ β_ (entry_size : nat) (entries : nat) :
    SimplifyGoalPlace l_ β_ (entries @ mpool entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mpool_unfold _ _)).

  Global Program Instance mpool_simplify_hyp_val_inst v_ (entry_size : nat) (entries : nat) :
    SimplifyHypVal v_ (entries @ mpool entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mpool_unfold _ _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mpool_simplify_goal_val_inst v_ (entry_size : nat) (entries : nat) :
    SimplifyGoalVal v_ (entries @ mpool entry_size)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mpool_unfold _ _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [sl_init]. *)
  Definition type_of_sl_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_spinlock)))); True)
      → ∃ gamma : lock_id, (void); (p ◁ₗ (spinlock (gamma))).

  (* Specifications for function [sl_lock]. *)
  Definition type_of_sl_lock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (spinlock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (spinlock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [round_pointer_up]. *)
  Definition type_of_round_pointer_up :=
    fn(∀ (p, size, align) : loc * loc * nat; (p @ (ptr)), (align @ (int (size_t))), (size @ (&own (uninit (size_t)))); True)
      → ∃ diff : nat, ((p +ₗ diff) @ (ptr)); (size ◁ₗ (diff @ (int (size_t)))) ∗ ⌜(p +ₗ diff) `aligned_to` align⌝ ∗ ⌜diff < align⌝.

  (* Specifications for function [mpool_add_chunk]. *)
  Definition type_of_mpool_add_chunk :=
    fn(∀ (p, q, n, entry_size, m) : loc * own_state * nat * nat * nat; (p @ (&frac{q} (n @ (mpool (entry_size))))), (&own (uninit (ly_with_align (m * entry_size) entry_size))), ((m * entry_size) @ (int (size_t))); True)
      → ∃ () : (), ((Z_of_bool (bool_decide (0 < m)%nat)) @ (int (bool_it))); (p ◁ₗ{q} (((n + m)%nat) @ (mpool (entry_size)))).

  (* Specifications for function [mpool_free]. *)
  Definition type_of_mpool_free :=
    fn(∀ (p, q, n, entry_size, ptr) : loc * own_state * nat * nat * loc; (p @ (&frac{q} (n @ (mpool (entry_size))))), (ptr @ (&own (uninit (ly_with_align entry_size entry_size)))); True)
      → ∃ () : (), (void); (p ◁ₗ{q} (((n + 1)%nat) @ (mpool (entry_size)))).

  (* Specifications for function [mpool_init]. *)
  Definition type_of_mpool_init :=
    fn(∀ (p, entry_size) : loc * nat; (p @ (&own (uninit (struct_mpool)))), (entry_size @ (int (size_t))); ⌜layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size⌝ ∗ ⌜layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size⌝ ∗ ⌜is_power_of_two entry_size⌝)
      → ∃ () : (), (void); (p ◁ₗ ((0%nat) @ (mpool (entry_size)))).

  (* Specifications for function [mpool_init_from]. *)
  Definition type_of_mpool_init_from :=
    fn(∀ (p, entry_size, q, entries, from) : loc * nat * own_state * nat * loc; (p @ (&own (uninit (struct_mpool)))), (from @ (&frac{q} (entries @ (mpool (entry_size))))); True)
      → ∃ rentries : nat, (void); (p ◁ₗ (rentries @ (mpool (entry_size)))) ∗ (from ◁ₗ{q} ((0%nat) @ (mpool (entry_size)))) ∗ ⌜q = Own → rentries = entries⌝.

  (* Specifications for function [mpool_init_with_fallback]. *)
  Definition type_of_mpool_init_with_fallback :=
    fn(∀ (p, entry_size, q, entries, fallback) : loc * nat * own_state * nat * loc; (p @ (&own (uninit (struct_mpool)))), (fallback @ (&shr (entries @ (mpool (entry_size))))); True)
      → ∃ () : (), (void); (p ◁ₗ ((0%nat) @ (mpool (entry_size)))).

  (* Specifications for function [mpool_fini]. *)
  Definition type_of_mpool_fini :=
    fn(∀ (p, n, entry_size) : loc * nat * nat; (p @ (&own (n @ (mpool (entry_size))))); True)
      → ∃ () : (), (void); (p ◁ₗ (uninit (struct_mpool))).

  (* Specifications for function [mpool_alloc_no_fallback]. *)
  Definition type_of_mpool_alloc_no_fallback :=
    fn(∀ (p, q, n, entry_size) : loc * own_state * nat * nat; (p @ (&frac{q} (n @ (mpool (entry_size))))); True)
      → ∃ b : bool, (b @ (optional (&own (uninit (ly_with_align entry_size entry_size))) null)); (p ◁ₗ{q} (((n-1)%nat) @ (mpool (entry_size)))) ∗ ⌜q = Own → b ↔ (0 < n)%nat⌝.

  (* Specifications for function [mpool_alloc]. *)
  Definition type_of_mpool_alloc :=
    fn(∀ (p, q, n, entry_size) : loc * own_state * nat * nat; (p @ (&frac{q} (n @ (mpool (entry_size))))); True)
      → ∃ b : bool, (b @ (optional (&own (uninit (ly_with_align entry_size entry_size))) null)); (p ◁ₗ{q} (((n-1)%nat) @ (mpool (entry_size)))) ∗ ⌜q = Own → (0 < n)%nat → b⌝.

  (* Specifications for function [mpool_alloc_contiguous_no_fallback]. *)
  Definition type_of_mpool_alloc_contiguous_no_fallback :=
    fn(∀ (p, q, n, entry_size, count, align) : loc * own_state * nat * nat * nat * nat; (p @ (&frac{q} (n @ (mpool (entry_size))))), (count @ (int (size_t))), (align @ (int (size_t))); ⌜(align * entry_size + count * entry_size)%Z ∈ size_t⌝ ∗ ⌜is_power_of_two align⌝)
      → ∃ n2 : nat, (optionalO (λ _ : unit,
        &own (uninit (ly_with_align (count * entry_size) (align * entry_size)))
      ) null); (p ◁ₗ{q} (n2 @ (mpool (entry_size)))) ∗ ⌜q = Own → n2 <= n⌝.

  (* Specifications for function [mpool_alloc_contiguous]. *)
  Definition type_of_mpool_alloc_contiguous :=
    fn(∀ (p, q, n, entry_size, count, align) : loc * own_state * nat * nat * nat * nat; (p @ (&frac{q} (n @ (mpool (entry_size))))), (count @ (int (size_t))), (align @ (int (size_t))); ⌜(align * entry_size + count * entry_size)%Z ∈ size_t⌝ ∗ ⌜is_power_of_two align⌝)
      → ∃ n2 : nat, (optionalO (λ _ : unit,
        &own (uninit (ly_with_align (count * entry_size) (align * entry_size)))
      ) null); (p ◁ₗ{q} (n2 @ (mpool (entry_size)))) ∗ ⌜q = Own → n2 <= n⌝.
End spec.

Typeclasses Opaque mpool_chunk_t_rec.
Typeclasses Opaque mpool_entry_t_rec.
Typeclasses Opaque mpool_rec.
