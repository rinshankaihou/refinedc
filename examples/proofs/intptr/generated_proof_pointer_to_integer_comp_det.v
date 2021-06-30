From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_pointer_to_integer_comp_det.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [pointer_to_integer_comp_det]. *)
  Lemma type_pointer_to_integer_comp_det :
    ⊢ typed_function impl_pointer_to_integer_comp_det type_of_pointer_to_integer_comp_det.
  Proof.
    Open Scope printing_sugar.
    start_function "pointer_to_integer_comp_det" ([]) => local_i local_x local_y local_j.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "pointer_to_integer_comp_det" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "pointer_to_integer_comp_det".
  Qed.
End proof_pointer_to_integer_comp_det.
