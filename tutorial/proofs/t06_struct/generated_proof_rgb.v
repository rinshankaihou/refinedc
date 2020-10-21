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
    start_function "rgb" ([[r g] b]) => arg_r arg_g arg_b.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "rgb" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "rgb".
  Qed.
End proof_rgb.
