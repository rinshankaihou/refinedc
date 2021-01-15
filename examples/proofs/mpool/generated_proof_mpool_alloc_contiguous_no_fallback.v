From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc_contiguous_no_fallback.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc_contiguous_no_fallback]. *)
  Lemma type_mpool_alloc_contiguous_no_fallback (global_round_pointer_up global_sl_lock global_sl_unlock : loc) :
    global_round_pointer_up ◁ᵥ global_round_pointer_up @ function_ptr type_of_round_pointer_up -∗
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_alloc_contiguous_no_fallback global_round_pointer_up global_sl_lock global_sl_unlock) type_of_mpool_alloc_contiguous_no_fallback.
  Proof.
    Open Scope printing_sugar.
    start_function "mpool_alloc_contiguous_no_fallback" ([[[[[p q] n] entry_size] count] align]) => arg_p arg_count arg_align local_prev local_before_start local_chunk_next local_new_chunk local_start local_ret local_chunk_size local_chunk.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      <[ "#1" :=
        ∃ pc : loc,
        ∃ entries_in_chunks1 : nat,
        ∃ entries_in_chunks2 : nat,
        ∃ entries_in_entry_list : nat,
        arg_count ◁ₗ (count @ (int (size_t))) ∗
        local_before_start ◁ₗ uninit (it_layout size_t) ∗
        local_chunk_next ◁ₗ uninit void* ∗
        local_new_chunk ◁ₗ uninit void* ∗
        local_start ◁ₗ uninit void* ∗
        local_chunk_size ◁ₗ uninit (it_layout size_t) ∗
        local_chunk ◁ₗ uninit void* ∗
        arg_align ◁ₗ ((align * entry_size) @ (int (size_t))) ∗
        local_ret ◁ₗ (null) ∗
        arg_p ◁ₗ (tyexists (λ l, place (l))) ∗
        local_prev ◁ₗ (pc @ (&own (entries_in_chunks2 @ (mpool_chunk_t (entry_size))))) ∗
        (p at{struct_mpool}ₗ "locked" ◁ₗ struct struct_mpool_locked_inner [wand_ex (λ x, pc ◁ₗ x @ mpool_chunk_t entry_size) (λ x, (entries_in_chunks1 + x)%nat @ mpool_chunk_t entry_size) ; entries_in_entry_list @ mpool_entry_t entry_size]) ∗
        ⌜shelve_hint (q = Own → n = (entries_in_chunks1 + entries_in_chunks2 + entries_in_entry_list)%nat)⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous_no_fallback" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by destruct o'; solve_goal.
    all: try by apply mult_le_compat_r; solve_goal.
    all: try by repeat progress rewrite /ly_size/=; have : (x4 - Z.to_nat o' - count > 0)%nat; solve_goal.
    all: print_sidecondition_goal "mpool_alloc_contiguous_no_fallback".
  Qed.
End proof_mpool_alloc_contiguous_no_fallback.
