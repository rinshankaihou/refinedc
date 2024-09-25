From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_talloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [talloc]. *)
  Lemma type_talloc (global_allocator_state global_sl_lock global_sl_unlock : loc) :
    global_locs !! "allocator_state" = Some global_allocator_state →
    global_initialized_types !! "allocator_state" = Some (GT (()) (λ '(), (alloc_state) : type)%I) →
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_talloc global_allocator_state global_sl_lock global_sl_unlock) type_of_talloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "talloc" (size) => arg_size local_prev local_cur local_ret.
    prepare_parameters (size).
    split_blocks ((
      <[ "#1" :=
        arg_size ◁ₗ (size @ (int (size_t))) ∗
        local_prev ◁ₗ uninit void* ∗
        local_cur ◁ₗ uninit void* ∗
        local_ret ◁ₗ uninit void* ∗
        (initialized "allocator_state" ())
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (BLOCK_PRECOND "#4") (λ _ : unit,
        ∃ pc : loc,
        local_prev ◁ₗ (pc @ (&own (alloc_entry_t))) ∗
        (global_allocator_state at{struct_alloc_state}ₗ "data" ◁ₗ wand (pc ◁ₗ alloc_entry_t) alloc_entry_t)
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "talloc" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "talloc" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: has_layout_loc_trans' => //; normalize_and_simpl_goal => //; apply: keep_factor2_leq; [solve_goal|]; apply Nat.divide_sub_r; apply Nat2Z.divide; rewrite /ly_align/ly_align_log/=; solve_goal.
    all: print_sidecondition_goal "talloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "talloc".
  Qed.
End proof_talloc.
