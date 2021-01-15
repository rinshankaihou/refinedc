From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_increment.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [increment]. *)
  Lemma type_increment (global_sl_lock global_sl_unlock : loc) :
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    global_sl_unlock ◁ᵥ global_sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_increment global_sl_lock global_sl_unlock) type_of_increment.
  Proof.
    Open Scope printing_sugar.
    start_function "increment" ([[[[p q] n1] n2] n3]) => arg_t local_ret.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "increment" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "increment".
  Qed.
End proof_increment.
