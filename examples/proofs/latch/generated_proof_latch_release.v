From refinedc.typing Require Import typing.
From refinedc.examples.latch Require Import generated_code.
From refinedc.examples.latch Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section proof_latch_release.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [latch_release]. *)
  Lemma type_latch_release :
    ⊢ typed_function impl_latch_release type_of_latch_release.
  Proof.
    Local Open Scope printing_sugar.
    start_function "latch_release" ([[p beta] P]) => arg_latch.
    prepare_parameters (p beta P).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "latch_release" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "latch_release".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "latch_release".
  Qed.
End proof_latch_release.
