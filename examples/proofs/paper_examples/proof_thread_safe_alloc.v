From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import code.
From refinedc.examples.paper_examples Require Import spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section proof_thread_safe_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [thread_safe_alloc]. *)
  Lemma type_thread_safe_alloc (data lock alloc sl_lock sl_unlock : loc) :
    global_locs !! "data" = Some data →
    global_locs !! "lock" = Some lock →
    global_initialized_types !! "data" = Some (GT lock_id (λ 'lid, (spinlocked (lid) ("data") (alloc_data)) : type)) →
    global_initialized_types !! "lock" = Some (GT lock_id (λ 'lid, (spinlock (lid)) : type)) →
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_thread_safe_alloc data lock alloc sl_lock sl_unlock) type_of_thread_safe_alloc.
  Proof.
    start_function "thread_safe_alloc" ([lid nsize]) => arg_size local_ret.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "thread_safe_alloc" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "thread_safe_alloc".
  Qed.
End proof_thread_safe_alloc.
