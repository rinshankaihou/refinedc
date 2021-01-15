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
  Lemma type_alloc (global_allocator_state global_sl_lock global_sl_unlock : loc) :
    global_locs !! "allocator_state" = Some global_allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT () (λ '(), (alloc_state) : type)) →
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_alloc global_allocator_state global_sl_lock global_sl_unlock) type_of_alloc.
  Proof.
    Open Scope printing_sugar.
    start_function "alloc" (size) => arg_size local_prev local_cur local_ret.
    split_blocks ((
      <[ "#1" :=
        arg_size ◁ₗ (size @ (int (size_t))) ∗
        local_prev ◁ₗ uninit void* ∗
        local_cur ◁ₗ uninit void* ∗
        local_ret ◁ₗ uninit void* ∗
        (initialized "allocator_state" ())
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      <[ "#4" :=
        ∃ pc : loc,
        arg_size ◁ₗ (size @ (int (size_t))) ∗
        local_cur ◁ₗ uninit void* ∗
        local_ret ◁ₗ uninit void* ∗
        local_prev ◁ₗ (pc @ (&own (alloc_entry_t))) ∗
        (global_allocator_state at{struct_alloc_state}ₗ "data" ◁ₗ wand (pc ◁ₗ alloc_entry_t) alloc_entry_t)
    ]> $
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "alloc".
  Qed.
End proof_alloc.
