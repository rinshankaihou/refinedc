From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import generated_code.
From refinedc.examples.spinlock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [examples/spinlock.c]. *)
Section proof_sl_unlock.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [sl_unlock]. *)
  Lemma type_sl_unlock :
    ⊢ typed_function impl_sl_unlock type_of_sl_unlock.
  Proof.
    Open Scope printing_sugar.
    start_function "sl_unlock" ([[p gamma] beta]) => arg_lock.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sl_unlock" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "sl_unlock".
  Qed.
End proof_sl_unlock.
