From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import generated_code.
From refinedc.examples.spinlock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [examples/spinlock.c]. *)
Section proof_sl_lock_both_same_prov.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [sl_lock_both_same_prov]. *)
  Lemma type_sl_lock_both_same_prov (global_sl_lock : loc) :
    global_sl_lock ◁ᵥ global_sl_lock @ function_ptr type_of_sl_lock -∗
    typed_function (impl_sl_lock_both_same_prov global_sl_lock) type_of_sl_lock_both_same_prov.
  Proof.
    Open Scope printing_sugar.
    start_function "sl_lock_both_same_prov" ([[[[[p2 gamma2] beta2] p1] gamma1] beta1]) => arg_a arg_b.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sl_lock_both_same_prov" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "sl_lock_both_same_prov".
  Qed.
End proof_sl_lock_both_same_prov.
