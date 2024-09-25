From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init (global_sl_init : loc) :
    global_sl_init ◁ᵥ global_sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_init global_sl_init) type_of_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init" (p) => arg_t.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init".
  Qed.
End proof_init.
