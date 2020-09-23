From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_init]. *)
  Lemma type_mpool_init (sl_init : loc) :
    sl_init ◁ᵥ sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_mpool_init sl_init) type_of_mpool_init.
  Proof.
    start_function "mpool_init" ([p entry_size]) => arg_p arg_entry_size.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_init".
  Qed.
End proof_mpool_init.
