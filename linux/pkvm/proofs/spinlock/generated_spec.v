From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
From refinedc.linux.pkvm.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/spinlock.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ} `{!spinlockG Σ}.

  (* Function [atomic_thread_fence] has been skipped. *)

  (* Function [atomic_signal_fence] has been skipped. *)

  (* Specifications for function [hyp_spin_lock_init]. *)
  Definition type_of_hyp_spin_lock_init :=
    fn(∀ p : loc; (p @ (&own (uninit (struct_hyp_spinlock)))); True)
      → ∃ id : lock_id, (void); (p ◁ₗ (hyp_spinlock_t (id))).

  (* Specifications for function [hyp_spin_lock]. *)
  Definition type_of_hyp_spin_lock :=
    fn(∀ (p, id, s) : loc * lock_id * own_state; (p @ (&frac{s} (hyp_spinlock_t (id)))); True)
      → ∃ () : (), (void); (p ◁ₗ{s} (hyp_spinlock_t (id))) ∗ (spinlock_token id []).

  (* Specifications for function [hyp_spin_unlock]. *)
  Definition type_of_hyp_spin_unlock :=
    fn(∀ (p, id, s) : loc * lock_id * own_state; (p @ (&frac{s} (hyp_spinlock_t (id)))); (spinlock_token id []))
      → ∃ () : (), (void); (p ◁ₗ{s} (hyp_spinlock_t (id))).
End spec.
