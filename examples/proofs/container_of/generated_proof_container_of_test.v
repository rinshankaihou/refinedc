From refinedc.typing Require Import typing.
From refinedc.examples.container_of Require Import generated_code.
From refinedc.examples.container_of Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/container_of.c]. *)
Section proof_container_of_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [container_of_test]. *)
  Lemma type_container_of_test :
    ⊢ typed_function impl_container_of_test type_of_container_of_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "container_of_test" ([]) => local_b local_t local_pt.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "container_of_test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "container_of_test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "container_of_test".
  Qed.
End proof_container_of_test.
