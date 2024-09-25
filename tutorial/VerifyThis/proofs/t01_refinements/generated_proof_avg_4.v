From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t01_refinements Require Import generated_code.
From refinedc.tutorial.VerifyThis.t01_refinements Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t01_refinements.c]. *)
Section proof_avg_4.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [avg_4]. *)
  Lemma type_avg_4 :
    ⊢ typed_function impl_avg_4 type_of_avg_4.
  Proof.
    Local Open Scope printing_sugar.
    start_function "avg_4" ([na nb]) => arg_a arg_b local_low local_high.
    prepare_parameters (na nb).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "avg_4" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "avg_4".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "avg_4".
  Qed.
End proof_avg_4.
