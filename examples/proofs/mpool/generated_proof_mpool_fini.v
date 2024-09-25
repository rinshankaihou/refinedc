From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_fini.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_fini]. *)
  Lemma type_mpool_fini (global_mpool_add_chunk global_mpool_free : loc) :
    global_mpool_add_chunk ◁ᵥ global_mpool_add_chunk @ function_ptr type_of_mpool_add_chunk -∗
    global_mpool_free ◁ᵥ global_mpool_free @ function_ptr type_of_mpool_free -∗
    typed_function (impl_mpool_fini global_mpool_add_chunk global_mpool_free) type_of_mpool_fini.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_fini" ([[p n] entry_size]) => arg_p local_size local_ptr1 local_ptr2 local_entry local_chunk.
    prepare_parameters (p n entry_size).
    split_blocks ((
      <[ "#5" :=
        local_size ◁ₗ uninit (it_layout size_t) ∗
        local_ptr1 ◁ₗ uninit void* ∗
        local_ptr2 ◁ₗ uninit void* ∗
        local_entry ◁ₗ (mpool_entry_t (entry_size)) ∗
        local_chunk ◁ₗ (mpool_chunk_t (entry_size)) ∗
        arg_p ◁ₗ (p @ (&own (struct (struct_mpool) [@{type} entry_size @ (int (size_t)) ; uninit (struct_spinlock) ; uninit (struct_mpool_locked_inner) ; &shr (∃ₜ n, n @ (mpool (entry_size))) ])))
    ]> $
      <[ "#2" :=
        local_size ◁ₗ uninit (it_layout size_t) ∗
        local_ptr1 ◁ₗ uninit void* ∗
        local_ptr2 ◁ₗ uninit void* ∗
        local_entry ◁ₗ (mpool_entry_t (entry_size)) ∗
        local_chunk ◁ₗ (mpool_chunk_t (entry_size)) ∗
        arg_p ◁ₗ (p @ (&own (struct (struct_mpool) [@{type} entry_size @ (int (size_t)) ; uninit (struct_spinlock) ; uninit (struct_mpool_locked_inner) ; &shr (∃ₜ n, n @ (mpool (entry_size))) ])))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#5".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_fini" "#2".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_fini".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_fini".
  Qed.
End proof_mpool_fini.
