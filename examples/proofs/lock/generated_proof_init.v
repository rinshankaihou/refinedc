From refinedc.typing Require Import typing.
From refinedc.examples.lock Require Import generated_code.
From refinedc.examples.lock Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
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
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
