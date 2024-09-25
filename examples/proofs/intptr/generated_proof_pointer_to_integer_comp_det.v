From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_pointer_to_integer_comp_det.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [pointer_to_integer_comp_det]. *)
  Lemma type_pointer_to_integer_comp_det :
    ⊢ typed_function impl_pointer_to_integer_comp_det type_of_pointer_to_integer_comp_det.
  Proof.
    Local Open Scope printing_sugar.
    start_function "pointer_to_integer_comp_det" ([]) => local_i local_x local_y local_j.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "pointer_to_integer_comp_det" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "pointer_to_integer_comp_det".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "pointer_to_integer_comp_det".
  Qed.
End proof_pointer_to_integer_comp_det.
