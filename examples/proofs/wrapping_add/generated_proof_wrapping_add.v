From refinedc.typing Require Import typing.
From refinedc.examples.wrapping_add Require Import generated_code.
From refinedc.examples.wrapping_add Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.wrapping_add Require Import wrapping_rules.
Set Default Proof Using "Type".

(* Generated from [examples/wrapping_add.c]. *)
Section proof_wrapping_add.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [wrapping_add]. *)
  Lemma type_wrapping_add :
    ⊢ typed_function impl_wrapping_add type_of_wrapping_add.
  Proof.
    Local Open Scope printing_sugar.
    start_function "wrapping_add" ([[a b] c]) => arg_a arg_b arg_c.
    prepare_parameters (a b c).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "wrapping_add" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "wrapping_add".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "wrapping_add".
  Qed.
End proof_wrapping_add.
