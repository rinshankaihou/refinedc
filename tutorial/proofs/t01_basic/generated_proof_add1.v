From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_add1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [add1]. *)
  Lemma type_add1 :
    ⊢ typed_function impl_add1 type_of_add1.
  Proof.
    Local Open Scope printing_sugar.
    start_function "add1" (n) => arg_a.
    prepare_parameters (n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "add1" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "add1".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "add1".
  Qed.
End proof_add1.
