From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_alloc_no_fallback.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_alloc_no_fallback]. *)
  Lemma type_mpool_alloc_no_fallback (global_sl_lock global_sl_unlock : loc) :
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_alloc_no_fallback global_sl_lock global_sl_unlock) type_of_mpool_alloc_no_fallback.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_alloc_no_fallback" ([[[p q] n] entry_size]) => arg_p local_new_chunk local_entry local_ret local_chunk.
    prepare_parameters (p q n entry_size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_alloc_no_fallback" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try (rewrite Z_distr_mul_sub_1; normalize_and_simpl_goal).
    all: try solve_goal; try (etrans; [done|]).
    all: try by rewrite /ly_size/=/ly_size/=; nia.
    all: print_sidecondition_goal "mpool_alloc_no_fallback".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_alloc_no_fallback".
  Qed.
End proof_mpool_alloc_no_fallback.
