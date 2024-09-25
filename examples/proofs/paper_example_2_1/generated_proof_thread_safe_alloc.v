From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_1 Require Import generated_code.
From refinedc.examples.paper_example_2_1 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section proof_thread_safe_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [thread_safe_alloc]. *)
  Lemma type_thread_safe_alloc (global_data global_lock global_alloc global_sl_lock global_sl_unlock : loc) :
    global_locs !! "data" = Some global_data →
    global_locs !! "lock" = Some global_lock →
    global_initialized_types !! "data" = Some (GT (lock_id) (λ 'lid, (tylocked (lid) ("data") (mem_t)) : type)%I) →
    global_initialized_types !! "lock" = Some (GT (lock_id) (λ 'lid, (spinlock (lid)) : type)%I) →
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_thread_safe_alloc global_data global_lock global_alloc global_sl_lock global_sl_unlock) type_of_thread_safe_alloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "thread_safe_alloc" ([lid n]) => arg_size local_ret.
    prepare_parameters (lid n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "thread_safe_alloc" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "thread_safe_alloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "thread_safe_alloc".
  Qed.
End proof_thread_safe_alloc.
