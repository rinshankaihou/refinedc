From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_int_to_ptr.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_to_ptr]. *)
  Lemma type_int_to_ptr :
    ⊢ typed_function impl_int_to_ptr type_of_int_to_ptr.
  Proof.
    Open Scope printing_sugar.
    start_function "int_to_ptr" (p) => arg_p local_q.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_to_ptr" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "int_to_ptr".
  Qed.
End proof_int_to_ptr.
