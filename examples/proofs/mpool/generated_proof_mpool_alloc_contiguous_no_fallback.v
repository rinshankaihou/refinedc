From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
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
    Local Open Scope printing_sugar.
    start_function "mpool_alloc_contiguous_no_fallback" ([[[[[p q] n] entry_size] count] align]) => arg_p arg_count arg_align local_prev local_before_start local_chunk_next local_new_chunk local_start local_ret local_chunk_size local_chunk.
    prepare_parameters (p q n entry_size count align).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (BLOCK_PRECOND "#1") (λ _ : unit,
        ∃ pc : loc,
        ∃ p_chunks : loc,
        ∃ entries_in_chunks2 : nat,
        ∃ entries_in_entry_list : nat,
        arg_align ◁ₗ ((align * entry_size) @ (int (size_t))) ∗
        local_ret ◁ₗ (null) ∗
        arg_p ◁ₗ (∃ₜ l, place (l)) ∗
        local_prev ◁ₗ (pc @ (&own (entries_in_chunks2 @ (mpool_chunk_t (entry_size))))) ∗
        (p at{struct_mpool}ₗ "locked" ◁ₗ struct struct_mpool_locked_inner [place p_chunks ; entries_in_entry_list @ mpool_entry_t entry_size]) ∗
        (p_chunks ◁ₗ (wand_ex (λ x,
          pc ◁ₗ x @ mpool_chunk_t entry_size
        ) (λ x,
          ∃ₜ entries_in_chunks1, constrained (((entries_in_chunks1 + x)%nat) @ (mpool_chunk_t (entry_size))) ⌜(q = Own → n = (entries_in_chunks1 + entries_in_chunks2 + entries_in_entry_list)%nat)⌝
        )))
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_contiguous_no_fallback" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try (etrans; [eassumption|]); repeat progress rewrite /has_layout_loc/ly_size/=.
    all: rewrite -?Nat.mul_sub_distr_r; try apply: Nat.mul_le_mono_r; try apply mul_le_mono_r_1.
    all: try by destruct o'; solve_goal.
    all: print_sidecondition_goal "mpool_alloc_contiguous_no_fallback".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_alloc_contiguous_no_fallback".
  Qed.
End proof_mpool_alloc_contiguous_no_fallback.
