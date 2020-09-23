From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import code.
From refinedc.examples.latch Require Import latch_def.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [latch_wait]. *)
  Definition type_of_latch_wait :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (latch (P)))); True)
      → ∃ () : (), (void); (p ◁ₗ{beta} (latch (P))) ∗ (P).

  (* Specifications for function [latch_release]. *)
  Definition type_of_latch_release :=
    fn(∀ (p, beta, P) : loc * own_state * (iProp Σ); (p @ (&frac{beta} (latch (P)))); (□ P))
      → ∃ () : (), (void); (p ◁ₗ{beta} (latch (P))).
End spec.
