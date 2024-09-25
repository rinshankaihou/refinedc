From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Definition of type [mpool_chunk_t]. *)
  Definition mpool_chunk_t_rec : (nat * nat → type) → (nat * nat → type) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      ∃ₜ (size : Z) (next : nat) (ly : layout),
      let local : nat := Z.to_nat (size `quot` entry_size) in
      constrained (padded (struct struct_mpool_chunk [@{type}
        (size @ (int (size_t))) ;
        (self (next, (entry_size)))
      ]) struct_mpool_chunk ly) (
        ⌜(entry_size | size)⌝ ∗
        ⌜(len = local + next)%nat⌝ ∗
        ⌜local > 0⌝ ∗
        ⌜ly = ly_with_align (Z.to_nat size) entry_size⌝
      )
    )) null))
  )%I.
  Global Typeclasses Opaque mpool_chunk_t_rec.

  Global Instance mpool_chunk_t_rec_le : TypeMono mpool_chunk_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_chunk_t (entry_size : nat) : rtype (nat) := {|
    rty r__ := mpool_chunk_t_rec (type_fixpoint mpool_chunk_t_rec) (r__, entry_size)
  |}.

  Lemma mpool_chunk_t_unfold (entry_size : nat) (len : nat):
    (len @ mpool_chunk_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        ∃ₜ (size : Z) (next : nat) (ly : layout),
        let local : nat := Z.to_nat (size `quot` entry_size) in
        constrained (padded (struct struct_mpool_chunk [@{type}
          (size @ (int (size_t))) ;
          (next @ (mpool_chunk_t (entry_size)))
        ]) struct_mpool_chunk ly) (
          ⌜(entry_size | size)⌝ ∗
          ⌜(len = local + next)%nat⌝ ∗
          ⌜local > 0⌝ ∗
          ⌜ly = ly_with_align (Z.to_nat size) entry_size⌝
        )
      )) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mpool_chunk_t_rec). Qed.

  Definition mpool_chunk_t_simplify_hyp_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_place_eq _ _ (mpool_chunk_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_chunk_t_simplify_hyp_place_inst_generated.
  Definition mpool_chunk_t_simplify_goal_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_place_eq _ _ (mpool_chunk_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_chunk_t_simplify_goal_place_inst_generated.

  Definition mpool_chunk_t_simplify_hyp_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_val_eq _ _ (mpool_chunk_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_chunk_t_simplify_hyp_val_inst_generated.
  Definition mpool_chunk_t_simplify_goal_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_val_eq _ _ (mpool_chunk_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_chunk_t_simplify_goal_val_inst_generated.

  (* Definition of type [mpool_entry_t]. *)
  Definition mpool_entry_t_rec : (nat * nat → type) → (nat * nat → type) := (λ self patt__,
    let len := patt__.1 in
    let entry_size := patt__.2 in
    (((0 < len)%nat) @ (optional (&own (
      ∃ₜ (nextlen : nat),
      constrained (padded (struct struct_mpool_entry [@{type}
        (self (nextlen, (entry_size)))
      ]) struct_mpool_entry (ly_with_align entry_size entry_size)) (
        ⌜len = S nextlen⌝
      )
    )) null))
  )%I.
  Global Typeclasses Opaque mpool_entry_t_rec.

  Global Instance mpool_entry_t_rec_le : TypeMono mpool_entry_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool_entry_t (entry_size : nat) : rtype (nat) := {|
    rty r__ := mpool_entry_t_rec (type_fixpoint mpool_entry_t_rec) (r__, entry_size)
  |}.

  Lemma mpool_entry_t_unfold (entry_size : nat) (len : nat):
    (len @ mpool_entry_t entry_size)%I ≡@{type} (
      (((0 < len)%nat) @ (optional (&own (
        ∃ₜ (nextlen : nat),
        constrained (padded (struct struct_mpool_entry [@{type}
          (nextlen @ (mpool_entry_t (entry_size)))
        ]) struct_mpool_entry (ly_with_align entry_size entry_size)) (
          ⌜len = S nextlen⌝
        )
      )) null))
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mpool_entry_t_rec). Qed.

  Definition mpool_entry_t_simplify_hyp_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_place_eq _ _ (mpool_entry_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_entry_t_simplify_hyp_place_inst_generated.
  Definition mpool_entry_t_simplify_goal_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_place_eq _ _ (mpool_entry_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_entry_t_simplify_goal_place_inst_generated.

  Definition mpool_entry_t_simplify_hyp_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_val_eq _ _ (mpool_entry_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_entry_t_simplify_hyp_val_inst_generated.
  Definition mpool_entry_t_simplify_goal_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_val_eq _ _ (mpool_entry_t_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_entry_t_simplify_goal_val_inst_generated.

  (* Definition of type [mpool]. *)
  Definition mpool_rec : (nat * nat → type) → (nat * nat → type) := (λ self patt__,
    let entries := patt__.1 in
    let entry_size := patt__.2 in
    ∃ₜ (lid : lock_id),
    constrained (struct struct_mpool [@{type}
      (entry_size @ (int (size_t))) ;
      (spinlock (lid)) ;
      ((tylocked_ex (lid) ("locked") (entries) (λ entries,
        ∃ₜ (entries_in_chunks : nat) (entries_in_entry_list : nat),
        constrained (struct struct_mpool_locked_inner [@{type}
          (entries_in_chunks @ (mpool_chunk_t (entry_size))) ;
          (entries_in_entry_list @ (mpool_entry_t (entry_size)))
        ]) (
          ⌜(entries = entries_in_chunks + entries_in_entry_list)%nat⌝
        )
      ))) ;
      (optionalO (λ _ : unit,
        &shr (∃ₜ n, self (n, (entry_size)))
      ) null)
    ]) (
      ⌜is_power_of_two entry_size⌝ ∗
      ⌜layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size⌝ ∗
      ⌜layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size⌝
    )
  )%I.
  Global Typeclasses Opaque mpool_rec.

  Global Instance mpool_rec_le : TypeMono mpool_rec.
  Proof. solve_type_proper. Qed.

  Definition mpool (entry_size : nat) : rtype (nat) := {|
    rty r__ := mpool_rec (type_fixpoint mpool_rec) (r__, entry_size)
  |}.

  Lemma mpool_unfold (entry_size : nat) (entries : nat):
    (entries @ mpool entry_size)%I ≡@{type} (
      ∃ₜ (lid : lock_id),
      constrained (struct struct_mpool [@{type}
        (entry_size @ (int (size_t))) ;
        (spinlock (lid)) ;
        ((tylocked_ex (lid) ("locked") (entries) (λ entries,
          ∃ₜ (entries_in_chunks : nat) (entries_in_entry_list : nat),
          constrained (struct struct_mpool_locked_inner [@{type}
            (entries_in_chunks @ (mpool_chunk_t (entry_size))) ;
            (entries_in_entry_list @ (mpool_entry_t (entry_size)))
          ]) (
            ⌜(entries = entries_in_chunks + entries_in_entry_list)%nat⌝
          )
        ))) ;
        (optionalO (λ _ : unit,
          &shr (∃ₜ n, n @ (mpool (entry_size)))
        ) null)
      ]) (
        ⌜is_power_of_two entry_size⌝ ∗
        ⌜layout_of struct_mpool_entry ⊑ ly_with_align entry_size entry_size⌝ ∗
        ⌜layout_of struct_mpool_chunk ⊑ ly_with_align entry_size entry_size⌝
      )
    )%I.
  Proof. apply: (type_fixpoint_unfold2 mpool_rec). Qed.

  Definition mpool_simplify_hyp_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_place_eq _ _ (mpool_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_simplify_hyp_place_inst_generated.
  Definition mpool_simplify_goal_place_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_place_eq _ _ (mpool_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_simplify_goal_place_inst_generated.

  Definition mpool_simplify_hyp_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_hyp_val_eq _ _ (mpool_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_simplify_hyp_val_inst_generated.
  Definition mpool_simplify_goal_val_inst_generated (entry_size : nat) patt__ :=
    [instance simplify_goal_val_eq _ _ (mpool_unfold (entry_size : nat) patt__) with 100%N].
  Global Existing Instance mpool_simplify_goal_val_inst_generated.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

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

  (* Specifications for function [round_pointer_up]. *)
  Definition type_of_round_pointer_up :=
    fn(∀ (p, size, align) : loc * loc * nat; (&own (place (p))), (align @ (int (size_t))), (size @ (&own (uninit (size_t)))); True)
      → ∃ diff : Z, (&own (place (p +ₗ diff))); (size ◁ₗ (diff @ (int (size_t)))) ∗ ⌜0 <= diff < align⌝ ∗ ⌜(p +ₗ diff) `aligned_to` align⌝.

  (* Specifications for function [mpool_add_chunk]. *)
  Definition type_of_mpool_add_chunk :=
    fn(∀ (p, q, n, entry_size, size) : loc * own_state * nat * nat * Z; (p @ (&frac{q} (n @ (mpool (entry_size))))), (&own (uninit (ly_with_align (Z.to_nat size) entry_size))), (size @ (int (size_t))); ⌜(entry_size | size)⌝)
      → ∃ () : (), ((bool_decide (0 < size)) @ (builtin_boolean)); (p ◁ₗ{q} (((n + (Z.to_nat (size `quot` entry_size)))%nat) @ (mpool (entry_size)))).

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

Notation "mpool_chunk_t< entry_size >" := (mpool_chunk_t entry_size)
  (only printing, format "'mpool_chunk_t<' entry_size '>'") : printing_sugar.
Notation "mpool_entry_t< entry_size >" := (mpool_entry_t entry_size)
  (only printing, format "'mpool_entry_t<' entry_size '>'") : printing_sugar.
Notation "mpool< entry_size >" := (mpool entry_size)
  (only printing, format "'mpool<' entry_size '>'") : printing_sugar.

Global Typeclasses Opaque mpool_chunk_t_rec.
Global Typeclasses Opaque mpool_chunk_t.
Global Typeclasses Opaque mpool_entry_t_rec.
Global Typeclasses Opaque mpool_entry_t.
Global Typeclasses Opaque mpool_rec.
Global Typeclasses Opaque mpool.
