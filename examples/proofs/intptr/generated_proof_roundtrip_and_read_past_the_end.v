From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_roundtrip_and_read_past_the_end.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [roundtrip_and_read_past_the_end]. *)
  Lemma type_roundtrip_and_read_past_the_end :
    ⊢ typed_function impl_roundtrip_and_read_past_the_end type_of_roundtrip_and_read_past_the_end.
  Proof.
    Local Open Scope printing_sugar.
    start_function "roundtrip_and_read_past_the_end" ([]) => local_x local_q local_p.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "roundtrip_and_read_past_the_end" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "roundtrip_and_read_past_the_end".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "roundtrip_and_read_past_the_end".
  Qed.
End proof_roundtrip_and_read_past_the_end.
