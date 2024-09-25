From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_hof.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_hof]. *)
  Lemma type_test_hof :
    ⊢ typed_function impl_test_hof type_of_test_hof.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_hof" ([]) => arg_f local_n1 local_n2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_hof" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_hof".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_hof".
  Qed.
End proof_test_hof.
