From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_min.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [min]. *)
  Lemma type_min :
    ⊢ typed_function impl_min type_of_min.
  Proof.
    Local Open Scope printing_sugar.
    start_function "min" ([a b]) => arg_a arg_b local_r.
    prepare_parameters (a b).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "min".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "min".
  Qed.
End proof_min.
