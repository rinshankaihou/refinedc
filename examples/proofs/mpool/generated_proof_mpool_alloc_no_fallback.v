From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc_no_fallback.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc_no_fallback]. *)
  Lemma type_mpool_alloc_no_fallback (sl_lock sl_unlock : loc) :
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_alloc_no_fallback sl_lock sl_unlock) type_of_mpool_alloc_no_fallback.
  Proof.
    start_function "mpool_alloc_no_fallback" ([[[p q] n] entry_size]) => arg_p local_new_chunk local_entry local_ret local_chunk.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_no_fallback" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by destruct x1 as [|[]]; try solve_goal; zify; ring_simplify; solve_goal.
    all: print_sidecondition_goal "mpool_alloc_no_fallback".
  Qed.
End proof_mpool_alloc_no_fallback.
