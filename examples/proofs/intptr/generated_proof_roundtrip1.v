From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_roundtrip1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [roundtrip1]. *)
  Lemma type_roundtrip1 :
    ⊢ typed_function impl_roundtrip1 type_of_roundtrip1.
  Proof.
    Open Scope printing_sugar.
    start_function "roundtrip1" (p) => arg_p local_i local_q.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "roundtrip1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "roundtrip1".
  Qed.
End proof_roundtrip1.
