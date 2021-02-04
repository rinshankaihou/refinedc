From refinedc.typing Require Import typing.
From refinedc.linux.pkvm.spinlock Require Import generated_code.
From refinedc.linux.pkvm.spinlock Require Import generated_spec.
From refinedc.linux.pkvm.spinlock Require Import spinlock_def.
From refinedc.linux.pkvm.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/spinlock.c]. *)
Section proof_hyp_spin_lock.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ} `{!spinlockG Σ}.

  (* Typing proof for [hyp_spin_lock]. *)
  Lemma type_hyp_spin_lock :
    ⊢ typed_function impl_hyp_spin_lock type_of_hyp_spin_lock.
  Proof. refine type_hyp_spin_lock. Qed.
End proof_hyp_spin_lock.
