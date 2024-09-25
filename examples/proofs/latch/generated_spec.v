From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Definition of type [latch]. *)
  Definition latch_rec : ((iProp Σ) → type) → ((iProp Σ) → type) := (λ self P,
    struct struct_latch [@{type}
      (atomic_bool (u8) ((□ P)) (True))
    ]
  )%I.
  Global Typeclasses Opaque latch_rec.

  Global Instance latch_rec_le : TypeMono latch_rec.
  Proof. solve_type_proper. Qed.

  Definition latch : rtype ((iProp Σ)) := {|
    rty r__ := latch_rec (type_fixpoint latch_rec) r__
  |}.

  Lemma latch_unfold (P : (iProp Σ)):
    (P @ latch)%I ≡@{type} (
      struct struct_latch [@{type}
        (atomic_bool (u8) ((□ P)) (True))
      ]
    )%I.
  Proof. apply: (type_fixpoint_unfold2 latch_rec). Qed.

  Definition latch_simplify_hyp_place_inst_generated patt__ :=
    [instance simplify_hyp_place_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_hyp_place_inst_generated.
  Definition latch_simplify_goal_place_inst_generated patt__ :=
    [instance simplify_goal_place_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_goal_place_inst_generated.

  Definition latch_simplify_hyp_val_inst_generated patt__ :=
    [instance simplify_hyp_val_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_hyp_val_inst_generated.
  Definition latch_simplify_goal_val_inst_generated patt__ :=
    [instance simplify_goal_val_eq _ _ (latch_unfold patt__) with 100%N].
  Global Existing Instance latch_simplify_goal_val_inst_generated.

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

Global Typeclasses Opaque latch_rec.
Global Typeclasses Opaque latch.
