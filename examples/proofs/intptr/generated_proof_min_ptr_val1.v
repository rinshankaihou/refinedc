From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_min_ptr_val1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [min_ptr_val1]. *)
  Lemma type_min_ptr_val1 :
    ⊢ typed_function impl_min_ptr_val1 type_of_min_ptr_val1.
  Proof.
    Open Scope printing_sugar.
    start_function "min_ptr_val1" ([p1 p2]) => arg_p1 arg_p2 local_i2 local_i1.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min_ptr_val1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "min_ptr_val1".
  Qed.
End proof_min_ptr_val1.
