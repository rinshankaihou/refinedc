From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_int_ptr2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_ptr2]. *)
  Lemma type_int_ptr2 :
    ⊢ typed_function impl_int_ptr2 type_of_int_ptr2.
  Proof.
    Open Scope printing_sugar.
    start_function "int_ptr2" (l) => arg_p local_i.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_ptr2" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "int_ptr2".
  Qed.
End proof_int_ptr2.
