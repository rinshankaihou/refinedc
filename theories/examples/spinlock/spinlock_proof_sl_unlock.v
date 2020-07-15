From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_code.
From refinedc.examples.spinlock Require Import spinlock_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [theories/examples/spinlock/spinlock.c]. *)
Section proof_sl_unlock.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [sl_unlock]. *)
  Lemma type_sl_unlock :
    ⊢ typed_function impl_sl_unlock type_of_sl_unlock.
  Proof. refine type_sl_unlock. Qed.
End proof_sl_unlock.
