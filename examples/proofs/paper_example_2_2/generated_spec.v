From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_2 Require Import generated_code.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_2.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Inlined code. *)

  Definition layout_of_nat : nat → layout := ly_set_size struct_chunk.
  Coercion layout_of_nat : nat >-> layout.

  Close Scope Z.

  (* Definition of type [chunks_t]. *)
  Definition chunks_t_rec : ((gmultiset nat) -d> typeO) → ((gmultiset nat) -d> typeO) := (λ self s,
    ((s ≠ ∅) @ (optional (&own (
      tyexists (λ n : nat,
      tyexists (λ tail : gmultiset nat,
      constrained (padded (struct struct_chunk [@{type}
        (n @ (int (size_t))) ;
        (guarded ("chunks_t_0") (apply_dfun self (tail)))
      ]) struct_chunk n) (
        ⌜s = {[n]} ⊎ tail⌝ ∗
        ⌜∀ k, k ∈ tail → n ≤ k⌝
      )))
    )) (null)))
  )%I.
  Typeclasses Opaque chunks_t_rec.

  Global Instance chunks_t_rec_ne : Contractive chunks_t_rec.
  Proof. solve_type_proper. Qed.

  Definition chunks_t : rtype := {|
    rty_type := (gmultiset nat);
    rty r__ := fixp chunks_t_rec r__
  |}.

  Lemma chunks_t_unfold (s : (gmultiset nat)):
    (s @ chunks_t)%I ≡@{type} (
      ((s ≠ ∅) @ (optional (&own (
        tyexists (λ n : nat,
        tyexists (λ tail : gmultiset nat,
        constrained (padded (struct struct_chunk [@{type}
          (n @ (int (size_t))) ;
          (guarded "chunks_t_0" (tail @ chunks_t))
        ]) struct_chunk n) (
          ⌜s = {[n]} ⊎ tail⌝ ∗
          ⌜∀ k, k ∈ tail → n ≤ k⌝
        )))
      )) (null)))
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance chunks_t_rmovable : RMovable chunks_t :=
    {| rmovable patt__ := movable_eq _ _ (chunks_t_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance chunks_t_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (chunks_t_unfold _)).
  Global Instance chunks_t_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (chunks_t_unfold _)).

  Global Program Instance chunks_t_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ chunks_t)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (chunks_t_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance chunks_t_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ chunks_t)%I (Some 100%N) :=
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
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))) ∗ (lock_token gamma []).

  (* Specifications for function [sl_unlock]. *)
  Definition type_of_sl_unlock :=
    fn(∀ (p, gamma, beta) : loc * lock_id * own_state; (p @ (&frac{beta} (spinlock (gamma)))); (lock_token gamma []))
      → ∃ () : (), (void); (p ◁ₗ{beta} (spinlock (gamma))).

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ (s, p, q, n) : (gmultiset nat) * loc * loc * nat; (p @ (&own (s @ (chunks_t)))), (q @ (&own (uninit (n)))), (n @ (int (size_t))); ⌜sizeof struct_chunk ≤ n⌝)
      → ∃ () : (), (void); (p ◁ₗ (({[n]} ⊎ s) @ (chunks_t))).
End spec.

Typeclasses Opaque chunks_t_rec.
