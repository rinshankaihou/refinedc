From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc]. *)
  Lemma type_mpool_alloc (mpool_alloc_no_fallback : loc) :
    mpool_alloc_no_fallback ◁ᵥ mpool_alloc_no_fallback @ function_ptr type_of_mpool_alloc_no_fallback -∗
    typed_function (impl_mpool_alloc mpool_alloc_no_fallback) type_of_mpool_alloc.
  Proof.
    start_function "mpool_alloc" ([[[p q] n] entry_size]) => arg_p local_ret.
    split_blocks ((
      <[ "#2" :=
        local_ret ◁ₗ uninit LPtr ∗
        arg_p ◁ₗ (optionalO (λ _ : unit,
          &shr (mpool (entry_size))
        ) null) ∗
        (p ◁ₗ{q} (((n - 1)%nat) @ (mpool (entry_size)))) ∗
        ⌜q = Own → n = 0%nat⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc" "#2".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_alloc".
  Qed.
End proof_mpool_alloc.
