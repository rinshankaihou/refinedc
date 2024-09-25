From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t01_refinements Require Import generated_code.
From refinedc.tutorial.VerifyThis.t01_refinements Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t01_refinements.c]. *)
Section proof_avg_3.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [avg_3]. *)
  Lemma type_avg_3 :
    ⊢ typed_function impl_avg_3 type_of_avg_3.
  Proof.
    Local Open Scope printing_sugar.
    start_function "avg_3" ([]) => arg_a arg_b local_low local_high.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "avg_3" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "avg_3".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "avg_3".
  Qed.
End proof_avg_3.
