From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import code.
From refinedc.examples.lock Require Import spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section proof_increment.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [increment]. *)
  Lemma type_increment (sl_lock sl_unlock : loc) :
    sl_lock ◁ᵥ sl_lock @ function_ptr type_of_sl_lock -∗
    sl_unlock ◁ᵥ sl_unlock @ function_ptr type_of_sl_unlock -∗
    typed_function (impl_increment sl_lock sl_unlock) type_of_increment.
  Proof.
    start_function "increment" ([[[[p q] n1] n2] n3]) => arg_t local_ret.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "increment" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "increment".
  Qed.
End proof_increment.
