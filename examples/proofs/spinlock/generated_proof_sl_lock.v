From refinedc.typing Require Import typing.
From refinedc.examples.spinlock Require Import generated_code.
From refinedc.examples.spinlock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.spinlock Require Import spinlock_proof.
Set Default Proof Using "Type".

(* Generated from [examples/spinlock.c]. *)
Section proof_sl_lock.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [sl_lock]. *)
  Lemma type_sl_lock :
    ⊢ typed_function impl_sl_lock type_of_sl_lock.
  Proof.
    Open Scope printing_sugar.
    start_function "sl_lock" ([[p gamma] beta]) => arg_lock local_expected.
    split_blocks ((
      <[ "#1" :=
        arg_lock ◁ₗ (p @ (&frac{beta} (spinlock (gamma)))) ∗
        local_expected ◁ₗ (false @ (boolean (bool_it)))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sl_lock" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "sl_lock" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "sl_lock".
  Qed.
End proof_sl_lock.
