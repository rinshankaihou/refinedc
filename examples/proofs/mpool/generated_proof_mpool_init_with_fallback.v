From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_init_with_fallback.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_init_with_fallback]. *)
  Lemma type_mpool_init_with_fallback (mpool_init : loc) :
    mpool_init ◁ᵥ mpool_init @ function_ptr type_of_mpool_init -∗
    typed_function (impl_mpool_init_with_fallback mpool_init) type_of_mpool_init_with_fallback.
  Proof.
    start_function "mpool_init_with_fallback" ([[[[p entry_size] q] entries] fallback]) => arg_p arg_fallback.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init_with_fallback" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_init_with_fallback".
  Qed.
End proof_mpool_init_with_fallback.
