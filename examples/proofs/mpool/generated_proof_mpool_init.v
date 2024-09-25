From refinedc.typing Require Import typing.
From refinedc.examples.mpool Require Import generated_code.
From refinedc.examples.mpool Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/mpool.c]. *)
Section proof_mpool_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [mpool_init]. *)
  Lemma type_mpool_init (global_sl_init : loc) :
    global_sl_init ◁ᵥ global_sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_mpool_init global_sl_init) type_of_mpool_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "mpool_init" ([p entry_size]) => arg_p arg_entry_size.
    prepare_parameters (p entry_size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "mpool_init".
  Qed.
End proof_mpool_init.
