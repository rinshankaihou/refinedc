From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_f.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_f]. *)
  Lemma type_test_f :
    ⊢ typed_function impl_test_f type_of_test_f.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_f" ([[l1 n] l2]) => arg_x arg_y.
    prepare_parameters (l1 n l2).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_f" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_f".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_f".
  Qed.
End proof_test_f.
