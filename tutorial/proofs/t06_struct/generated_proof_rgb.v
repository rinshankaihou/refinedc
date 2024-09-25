From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_rgb.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [rgb]. *)
  Lemma type_rgb :
    ⊢ typed_function impl_rgb type_of_rgb.
  Proof.
    Local Open Scope printing_sugar.
    start_function "rgb" ([[r g] b]) => arg_r arg_g arg_b.
    prepare_parameters (r g b).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "rgb" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "rgb".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "rgb".
  Qed.
End proof_rgb.
