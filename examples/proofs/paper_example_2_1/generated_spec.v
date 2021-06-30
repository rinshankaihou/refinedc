From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_1 Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
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

  Lemma mem_t_unfold (a : nat):
    (a @ mem_t)%I ≡@{type} (
      struct struct_mem_t [@{type}
        (a @ (int (size_t))) ;
        (&own (uninit (a)))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance mem_t_rmovable : RMovable mem_t :=
    {| rmovable patt__ := movable_eq _ _ (mem_t_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance mem_t_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (mem_t_unfold _)).
  Global Instance mem_t_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (mem_t_unfold _)).

  Global Program Instance mem_t_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (mem_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance mem_t_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ mem_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (mem_t_unfold _) T _).
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
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (lock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (lock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [sl_lock_both]. *)
  Definition type_of_sl_lock_both :=
    fn(∀ (p2, gamma2, beta2, p1, gamma1, beta1) : loc * lock_id * own_state * loc * lock_id * own_state; (p2 @ (&frac{beta2} (spinlock (gamma2)))), (p1 @ (&frac{beta1} (spinlock (gamma1)))); True)
      → ∃ () : (), (void); (p2 ◁ₗ{beta2} (spinlock (gamma2))) ∗ (lock_token gamma2 []) ∗ (p1 ◁ₗ{beta1} (spinlock (gamma1))) ∗ (lock_token gamma1 []).

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ (a, n, p) : nat * nat * loc; (p @ (&own (a @ (mem_t)))), (n @ (int (size_t))); True)
      → ∃ () : (), ((n ≤ a) @ (optional (&own (uninit (n))) (null))); (p ◁ₗ ((n ≤ a ? a - n : a) @ (mem_t))).

  (* Specifications for function [alloc_from_start]. *)
  Definition type_of_alloc_from_start :=
    fn(∀ (a, n, p) : nat * nat * loc; (p @ (&own (a @ (mem_t)))), (n @ (int (size_t))); True)
      → ∃ () : (), ((n ≤ a) @ (optional (&own (uninit (n))) (null))); (p ◁ₗ ((n ≤ a ? a - n : a) @ (mem_t))).

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
