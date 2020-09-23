From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc_contiguous.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc_contiguous]. *)
  Lemma type_mpool_alloc_contiguous (mpool_alloc_contiguous_no_fallback : loc) :
    mpool_alloc_contiguous_no_fallback ◁ᵥ mpool_alloc_contiguous_no_fallback @ function_ptr type_of_mpool_alloc_contiguous_no_fallback -∗
    typed_function (impl_mpool_alloc_contiguous mpool_alloc_contiguous_no_fallback) type_of_mpool_alloc_contiguous.
  Proof.
    start_function "mpool_alloc_contiguous" ([[[[[p q] n] entry_size] count] align]) => arg_p arg_count arg_align local_ret.
    split_blocks ((
      <[ "#2" :=
        ∃ n2 : nat,
        arg_count ◁ₗ (count @ (int (size_t))) ∗
        arg_align ◁ₗ (align @ (int (size_t))) ∗
        local_ret ◁ₗ uninit LPtr ∗
        arg_p ◁ₗ (optionalO (λ _ : unit,
          &shr (mpool (entry_size))
        ) null) ∗
        (p ◁ₗ{q} (n2 @ (mpool (entry_size)))) ∗
        ⌜q = Own → n2 <= n⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous" "#2".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_alloc_contiguous".
  Qed.
End proof_mpool_alloc_contiguous.
