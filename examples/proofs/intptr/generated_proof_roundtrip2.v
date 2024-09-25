From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_roundtrip2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [roundtrip2]. *)
  Lemma type_roundtrip2 :
    ⊢ typed_function impl_roundtrip2 type_of_roundtrip2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "roundtrip2" (p) => arg_p local_i local_q.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "roundtrip2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "roundtrip2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "roundtrip2".
  Qed.
End proof_roundtrip2.
