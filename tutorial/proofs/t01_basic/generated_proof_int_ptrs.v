From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_int_ptrs.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_ptrs]. *)
  Lemma type_int_ptrs :
    ⊢ typed_function impl_int_ptrs type_of_int_ptrs.
  Proof.
    Local Open Scope printing_sugar.
    start_function "int_ptrs" ([p1 p2]) => arg_p1 arg_p2.
    prepare_parameters (p1 p2).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_ptrs" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "int_ptrs".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "int_ptrs".
  Qed.
End proof_int_ptrs.
