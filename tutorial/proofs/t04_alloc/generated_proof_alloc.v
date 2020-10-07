From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc]. *)
  Lemma type_alloc (allocator_state sl_lock sl_unlock : loc) :
    global_locs !! "allocator_state" = Some allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT () (λ '(), (alloc_state) : type)) →
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_alloc allocator_state sl_lock sl_unlock) type_of_alloc.
  Proof.
    start_function "alloc" (size) => arg_size local_prev local_cur local_ret.
    split_blocks ((
      <[ "#1" :=
        arg_size ◁ₗ (size @ (int (size_t))) ∗
        local_prev ◁ₗ uninit LPtr ∗
        local_cur ◁ₗ uninit LPtr ∗
        local_ret ◁ₗ uninit LPtr ∗
        (initialized "allocator_state" ())
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      <[ "#4" :=
        ∃ pc : loc,
        arg_size ◁ₗ (size @ (int (size_t))) ∗
        local_cur ◁ₗ uninit LPtr ∗
        local_ret ◁ₗ uninit LPtr ∗
        local_prev ◁ₗ (pc @ (&own (alloc_entry_t))) ∗
        (allocator_state at{struct_alloc_state}ₗ "data" ◁ₗ wand (pc ◁ₗ alloc_entry_t) alloc_entry_t)
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "alloc".
  Qed.
End proof_alloc.