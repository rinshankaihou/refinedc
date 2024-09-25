From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_logical.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_logical]. *)
  Lemma type_test_logical :
    ⊢ typed_function impl_test_logical type_of_test_logical.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_logical" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_logical" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_logical".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_logical".
  Qed.
End proof_test_logical.
