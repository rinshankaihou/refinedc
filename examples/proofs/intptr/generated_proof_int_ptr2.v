From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_int_ptr2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_ptr2]. *)
  Lemma type_int_ptr2 :
    ⊢ typed_function impl_int_ptr2 type_of_int_ptr2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "int_ptr2" (l) => arg_p local_i.
    prepare_parameters (l).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_ptr2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "int_ptr2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "int_ptr2".
  Qed.
End proof_int_ptr2.
