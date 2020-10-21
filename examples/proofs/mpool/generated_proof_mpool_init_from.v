From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_init_from.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_init_from]. *)
  Lemma type_mpool_init_from (mpool_init sl_lock sl_unlock : loc) :
    mpool_init ◁ᵥ mpool_init @ function_ptr type_of_mpool_init -∗
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_init_from mpool_init sl_lock sl_unlock) type_of_mpool_init_from.
  Proof.
    start_function "mpool_init_from" ([[[[p entry_size] q] entries] from]) => arg_p arg_from.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init_from" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_init_from".
  Qed.
End proof_mpool_init_from.
