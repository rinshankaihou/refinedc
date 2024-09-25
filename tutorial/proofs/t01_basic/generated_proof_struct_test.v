From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_struct_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [struct_test]. *)
  Lemma type_struct_test :
    ⊢ typed_function impl_struct_test type_of_struct_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "struct_test" (p) => arg_out.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "struct_test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "struct_test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "struct_test".
  Qed.
End proof_struct_test.
