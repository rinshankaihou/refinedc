From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_add_chunk.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_add_chunk]. *)
  Lemma type_mpool_add_chunk (global_sl_lock global_sl_unlock : loc) :
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_add_chunk global_sl_lock global_sl_unlock) type_of_mpool_add_chunk.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_add_chunk" ([[[[p q] n] entry_size] size]) => arg_p arg_begin arg_size local_chunk.
    prepare_parameters (p q n entry_size size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_add_chunk" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_add_chunk".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_add_chunk".
  Qed.
End proof_mpool_add_chunk.
