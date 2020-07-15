From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import lock_code.
From refinedc.examples.lock Require Import lock_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [theories/examples/lock/lock.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init (sl_init : loc) :
    sl_init ◁ᵥ sl_init @ function_ptr type_of_sl_init -∗
    typed_function (impl_init sl_init) type_of_init.
  Proof.
    start_function "init" (p) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
