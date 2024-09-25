From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_roundtrip_and_read1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [roundtrip_and_read1]. *)
  Lemma type_roundtrip_and_read1 :
    ⊢ typed_function impl_roundtrip_and_read1 type_of_roundtrip_and_read1.
  Proof.
    Local Open Scope printing_sugar.
    start_function "roundtrip_and_read1" ([l n]) => arg_p local_i local_r local_q.
    prepare_parameters (l n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "roundtrip_and_read1" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "roundtrip_and_read1".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "roundtrip_and_read1".
  Qed.
End proof_roundtrip_and_read1.
