From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
From refinedc.examples.latch Require Import generated_spec.
From refinedc.examples.latch Require Import latch_def.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section proof_latch_release.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [latch_release]. *)
  Lemma type_latch_release :
    ⊢ typed_function impl_latch_release type_of_latch_release.
  Proof.
    start_function "latch_release" ([[p beta] P]) => arg_latch.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "latch_release" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "latch_release".
  Qed.
End proof_latch_release.
