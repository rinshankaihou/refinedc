From refinedc.typing Require Import typing.
From refinedc.examples.wrapping_add Require Import generated_code.
From refinedc.examples.wrapping_add Require Import generated_spec.
From refinedc.examples.wrapping_add Require Import wrapping_rules.
Set Default Proof Using "Type".

(* Generated from [examples/wrapping_add.c]. *)
Section proof_wrapping_add.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [wrapping_add]. *)
  Lemma type_wrapping_add :
    ⊢ typed_function impl_wrapping_add type_of_wrapping_add.
  Proof.
    start_function "wrapping_add" ([[a b] c]) => arg_a arg_b arg_c.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "wrapping_add" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "wrapping_add".
  Qed.
End proof_wrapping_add.
