From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_fini.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_fini]. *)
  Lemma type_mpool_fini (mpool_add_chunk mpool_free : loc) :
    mpool_add_chunk ◁ᵥ mpool_add_chunk @ function_ptr type_of_mpool_add_chunk -∗
    mpool_free ◁ᵥ mpool_free @ function_ptr type_of_mpool_free -∗
    typed_function (impl_mpool_fini mpool_add_chunk mpool_free) type_of_mpool_fini.
  Proof.
    start_function "mpool_fini" ([[p n] entry_size]) => arg_p local_size local_ptr1 local_ptr2 local_entry local_chunk.
    split_blocks ((
      <[ "#5" :=
        local_size ◁ₗ uninit (it_layout size_t) ∗
        local_ptr1 ◁ₗ uninit LPtr ∗
        local_ptr2 ◁ₗ uninit LPtr ∗
        local_entry ◁ₗ (mpool_entry_t (entry_size)) ∗
        local_chunk ◁ₗ (mpool_chunk_t (entry_size)) ∗
        arg_p ◁ₗ (p @ (&own (struct (struct_mpool) [@{type} entry_size @ (int (size_t)) ; uninit (struct_spinlock) ; uninit (struct_mpool_locked_inner) ; &shr (tyexists (λ n, n @ (mpool (entry_size)))) ])))
    ]> $
      <[ "#2" :=
        local_size ◁ₗ uninit (it_layout size_t) ∗
        local_ptr1 ◁ₗ uninit LPtr ∗
        local_ptr2 ◁ₗ uninit LPtr ∗
        local_entry ◁ₗ (mpool_entry_t (entry_size)) ∗
        local_chunk ◁ₗ (mpool_chunk_t (entry_size)) ∗
        arg_p ◁ₗ (p @ (&own (struct (struct_mpool) [@{type} entry_size @ (int (size_t)) ; uninit (struct_spinlock) ; uninit (struct_mpool_locked_inner) ; &shr (tyexists (λ n, n @ (mpool (entry_size)))) ])))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#5".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#2".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_fini".
  Qed.
End proof_mpool_fini.
