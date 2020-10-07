From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_add_chunk.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_add_chunk]. *)
  Lemma type_mpool_add_chunk (sl_lock sl_unlock : loc) :
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_add_chunk sl_lock sl_unlock) type_of_mpool_add_chunk.
  Proof.
    start_function "mpool_add_chunk" ([[[[p q] n] entry_size] m]) => arg_p arg_begin arg_size local_chunk.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_add_chunk" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by destruct m => //=; solve_goal.
    all: print_sidecondition_goal "mpool_add_chunk".
  Qed.
End proof_mpool_add_chunk.