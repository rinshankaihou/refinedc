From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
From refinedc.examples.latch Require Import generated_spec.
From refinedc.examples.latch Require Import latch_def.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section proof_latch_wait.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [latch_wait]. *)
  Lemma type_latch_wait :
    ⊢ typed_function impl_latch_wait type_of_latch_wait.
  Proof.
    Open Scope printing_sugar.
    start_function "latch_wait" ([[p beta] P]) => arg_latch.
    split_blocks ((
      <[ "#1" :=
        arg_latch ◁ₗ (p @ (&frac{beta} (latch (P))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "latch_wait" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "latch_wait" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "latch_wait".
  Qed.
End proof_latch_wait.
