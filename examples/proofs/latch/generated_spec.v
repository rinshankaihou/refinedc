From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [latch]. *)
  Definition latch_rec : ((iProp Σ) -d> typeO) → ((iProp Σ) -d> typeO) := (λ self P,
    struct struct_latch [@{type}
      (atomic_bool (bool_it) ((□ P)) (True))
    ]
  )%I.
  Typeclasses Opaque latch_rec.

  Global Instance latch_rec_ne : Contractive latch_rec.
  Proof. solve_type_proper. Qed.

  Definition latch : rtype := {|
    rty_type := (iProp Σ);
    rty r__ := fixp latch_rec r__
  |}.

  Lemma latch_unfold (P : (iProp Σ)):
    (P @ latch)%I ≡@{type} (
      struct struct_latch [@{type}
        (atomic_bool (bool_it) ((□ P)) (True))
      ]
    )%I.
  Proof. by rewrite {1}/with_refinement/=fixp_unfold. Qed.


  Global Program Instance latch_rmovable : RMovable latch :=
    {| rmovable patt__ := movable_eq _ _ (latch_unfold patt__) |}.
  Next Obligation. solve_ty_layout_eq. Qed.

  Global Instance latch_simplify_hyp_place_inst_generated l_ β_ patt__:
    SimplifyHypPlace l_ β_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_place_eq l_ β_ _ _ T (latch_unfold _)).
  Global Instance latch_simplify_goal_place_inst_generated l_ β_ patt__:
    SimplifyGoalPlace l_ β_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_place_eq l_ β_ _ _ T (latch_unfold _)).

  Global Program Instance latch_simplify_hyp_val_inst_generated v_ patt__:
    SimplifyHypVal v_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_hyp_val_eq v_ _ _ (latch_unfold _) T _).
  Next Obligation. done. Qed.
  Global Program Instance latch_simplify_goal_val_inst_generated v_ patt__:
    SimplifyGoalVal v_ (patt__ @ latch)%I (Some 100%N) :=
    λ T, i2p (simplify_goal_val_eq v_ _ _ (latch_unfold _) T _).
  Next Obligation. done. Qed.

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [latch_wait]. *)
  Definition type_of_latch_wait :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (P @ (latch)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (P @ (latch))) ∗ (P).

  (* Specifications for function [latch_release]. *)
  Definition type_of_latch_release :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (P @ (latch)))); (□ P))
      → ∃ () : (), (void); (p ◁ₗ{beta} (P @ (latch))).
End spec.

Typeclasses Opaque latch_rec.
