From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_read_locked.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [read_locked]. *)
  Lemma type_read_locked (sl_lock sl_unlock : loc) :
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_read_locked sl_lock sl_unlock) type_of_read_locked.
  Proof.
    start_function "read_locked" ([[[[p q] n1] n2] n3]) => arg_t local_ret.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "read_locked" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "read_locked".
  Qed.
End proof_read_locked.
