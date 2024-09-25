From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_roundtrip_and_read_past_the_end_copy_alloc_id.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [roundtrip_and_read_past_the_end_copy_alloc_id]. *)
  Lemma type_roundtrip_and_read_past_the_end_copy_alloc_id (global_copy_alloc_id : loc) :
    global_copy_alloc_id ◁ᵥ global_copy_alloc_id @ inline_function_ptr impl_copy_alloc_id -∗
    typed_function (impl_roundtrip_and_read_past_the_end_copy_alloc_id global_copy_alloc_id) type_of_roundtrip_and_read_past_the_end_copy_alloc_id.
  Proof.
    Local Open Scope printing_sugar.
    start_function "roundtrip_and_read_past_the_end_copy_alloc_id" ([]) => local_x local_q local_p local_pi.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "roundtrip_and_read_past_the_end_copy_alloc_id" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "roundtrip_and_read_past_the_end_copy_alloc_id".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "roundtrip_and_read_past_the_end_copy_alloc_id".
  Qed.
End proof_roundtrip_and_read_past_the_end_copy_alloc_id.
