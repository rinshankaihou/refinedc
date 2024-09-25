From refinedc.typing Require Import typing.
From refinedc.examples.intptr Require Import generated_code.
From refinedc.examples.intptr Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section proof_cast_NULL.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [cast_NULL]. *)
  Lemma type_cast_NULL :
    ⊢ typed_function impl_cast_NULL type_of_cast_NULL.
  Proof.
    Local Open Scope printing_sugar.
    start_function "cast_NULL" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "cast_NULL" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "cast_NULL".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "cast_NULL".
  Qed.
End proof_cast_NULL.