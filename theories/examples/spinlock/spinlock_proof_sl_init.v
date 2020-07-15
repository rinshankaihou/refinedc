From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import spinlock_code.
From refinedc.examples.spinlock Require Import spinlock_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [theories/examples/spinlock/spinlock.c]. *)
Section proof_sl_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [sl_init]. *)
  Lemma type_sl_init :
    ⊢ typed_function impl_sl_init type_of_sl_init.
  Proof. refine type_sl_init. Qed.
End proof_sl_init.
