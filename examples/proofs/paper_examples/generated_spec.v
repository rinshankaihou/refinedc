From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Notation "P ? l : r" :=
    (if bool_decide P then l else r)
    (at level 100, l at next level, r at next level).

  Close Scope Z.

  Definition byte_layout : nat → layout := ly_set_size u8.
  Coercion byte_layout : nat >-> layout.

  (* Definition of type [mem_t]. *)
  Definition mem_t_rec : (nat -d> typeO) → (nat -d> typeO) := (λ self a,
    struct struct_mem_t [@{type}
      (a @ (int (size_t))) ;
      (&own (uninit (a)))
    ]
  )%I.
  Typeclasses Opaque mem_t_rec.

  Global Instance mem_t_rec_ne : Contractive mem_t_rec.
  Proof. solve_type_proper. Qed.

  Definition mem_t : rtype := {|
    rty_type := nat;
    rty r__ := fixp mem_t_rec r__
  |}.

  Lemma mem_t_unfold (a : nat) :
    (a @ mem_t)%I ≡@{type} (
      struct struct_mem_t [@{type}
        (a @ (int (size_t))) ;
        (&own (uninit (a)))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mem_t_rmovable : RMovable mem_t :=
    {| rmovable 'a := movable_eq _ _ (mem_t_unfold a) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mem_t_simplify_hyp_place_inst l_ β_ (a : nat) :
    SimplifyHypPlace l_ β_ (a @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mem_t_unfold _)).
  Global Instance mem_t_simplify_goal_place_inst l_ β_ (a : nat) :
    SimplifyGoalPlace l_ β_ (a @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mem_t_unfold _)).

  Global Program Instance mem_t_simplify_hyp_val_inst v_ (a : nat) :
    SimplifyHypVal v_ (a @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mem_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mem_t_simplify_goal_val_inst v_ (a : nat) :
    SimplifyGoalVal v_ (a @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mem_t_unfold _) T _).
  Next Obligation. done. Qed.

  (* Definition of type [chunks_t]. *)
  Definition chunks_t_rec : ((gmultiset layout) -d> typeO) → ((gmultiset layout) -d> typeO) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      tyexists (λ ly : layout,
      tyexists (λ tail : gmultiset layout,
      constrained (padded (struct struct_chunk [@{type}
        ((ly.(ly_size)) @ (int (size_t))) ;
        (guarded ("chunks_t_0") (apply_dfun self (tail)))
      ]) struct_chunk ly) (
        ⌜s = {[ly]} ⊎ tail⌝ ∗
        ⌜∀ k, k ∈ tail → ly.(ly_size) ≤ k.(ly_size)⌝
      )))
    )) (null)))
  )%I.
  Typeclasses Opaque chunks_t_rec.

  Global Instance chunks_t_rec_ne : Contractive chunks_t_rec.
  Proof. solve_type_proper. Qed.

  Definition chunks_t : rtype := {|
    rty_type := (gmultiset layout);
    rty r__ := fixp chunks_t_rec r__
  |}.

  Lemma chunks_t_unfold (s : gmultiset layout) :
    (s @ chunks_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        tyexists (λ ly : layout,
        tyexists (λ tail : gmultiset layout,
        constrained (padded (struct struct_chunk [@{type}
          ((ly.(ly_size)) @ (int (size_t))) ;
          (guarded "chunks_t_0" (tail @ chunks_t))
        ]) struct_chunk ly) (
          ⌜s = {[ly]} ⊎ tail⌝ ∗
          ⌜∀ k, k ∈ tail → ly.(ly_size) ≤ k.(ly_size)⌝
        )))
      )) (null)))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance chunks_t_rmovable : RMovable chunks_t :=
    {| rmovable 's := movable_eq _ _ (chunks_t_unfold s) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance chunks_t_simplify_hyp_place_inst l_ β_ (s : gmultiset layout) :
    SimplifyHypPlace l_ β_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (chunks_t_unfold _)).
  Global Instance chunks_t_simplify_goal_place_inst l_ β_ (s : gmultiset layout) :
    SimplifyGoalPlace l_ β_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (chunks_t_unfold _)).

  Global Program Instance chunks_t_simplify_hyp_val_inst v_ (s : gmultiset layout) :
    SimplifyHypVal v_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (chunks_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance chunks_t_simplify_goal_val_inst v_ (s : gmultiset layout) :
    SimplifyGoalVal v_ (s @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (chunks_t_unfold _) T _).
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

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ (a, n, p) : nat * nat * loc; (p @ (&own (a @ (mem_t)))), (n @ (int (size_t))); True)
      → ∃ () : (), ((n ≤ a) @ (optional (&own (uninit (n))) (null))); (p ◁ₗ ((n ≤ a ? a - n : a) @ (mem_t))).

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ (s, p, ly) : (gmultiset layout) * loc * layout; (p @ (&own (s @ (chunks_t)))), (&own (uninit (ly))), ((ly.(ly_size)) @ (int (size_t))); ⌜layout_of struct_chunk ⊑ ly⌝)
      → ∃ () : (), (void); (p ◁ₗ (({[ly]} ⊎ s) @ (chunks_t))).

  (* Specifications for function [thread_safe_alloc]. *)
  Definition type_of_thread_safe_alloc :=
    fn(∀ (lid, n) : lock_id * nat; (n @ (int (size_t))); (initialized "lock" lid) ∗ (initialized "data" lid))
      → ∃ () : (), (optionalO (λ _ : unit,   &own (uninit (n))
      ) (null)); True.

  (* Specifications for function [fork]. *)
  Definition type_of_fork :=
    fn(∀ (ty, P) : type * (iProp Σ); (function_ptr (fn(∀ () : (); &own ty; P) → ∃ () : (), void; True)), (&own (ty)); (P))
      → ∃ () : (), (void); True.

  (* Specifications for function [test_thread_safe_alloc_fork_fn]. *)
  Definition type_of_test_thread_safe_alloc_fork_fn :=
    fn(∀ () : (); (&own (tyexists (λ n : nat, n @ (int (size_t))))); (∃ lid : gname, initialized "lock" lid ∗ initialized "data" lid))
      → ∃ () : (), (void); True.

  (* Specifications for function [test_thread_safe_alloc]. *)
  Definition type_of_test_thread_safe_alloc :=
    fn(∀ lid : gname; (initialized "lock" lid) ∗ (initialized "data" lid) ∗ (global_with_type "param" Own (uninit size_t)))
      → ∃ () : (), (void); True.
End spec.

Typeclasses Opaque mem_t_rec.
Typeclasses Opaque chunks_t_rec.
