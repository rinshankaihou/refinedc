From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import latch_code.
From refinedc.examples.latch Require Import latch_spec.
From refinedc.examples.latch Require Import latch_def.
Set Default Proof Using "Type".

(* Generated from [theories/examples/latch/latch.c]. *)
Section proof_latch_release.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [latch_release]. *)
  Lemma type_latch_release :
    ⊢ typed_function impl_latch_release type_of_latch_release.
  Proof.
    start_function "latch_release" ([[p beta] P]) => arg_latch.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "latch_release" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "latch_release".
  Qed.
End proof_latch_release.
