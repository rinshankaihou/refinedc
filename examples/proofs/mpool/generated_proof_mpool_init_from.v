From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_init_from.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_init_from]. *)
  Lemma type_mpool_init_from (global_mpool_init global_sl_lock global_sl_unlock : loc) :
    global_mpool_init ◁ᵥ global_mpool_init @ function_ptr type_of_mpool_init -∗
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_mpool_init_from global_mpool_init global_sl_lock global_sl_unlock) type_of_mpool_init_from.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_init_from" ([[[[p entry_size] q] entries] from]) => arg_p arg_from.
    prepare_parameters (p entry_size q entries from).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init_from" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_init_from".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_init_from".
  Qed.
End proof_mpool_init_from.
