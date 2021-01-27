From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_ternary.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_ternary]. *)
  Lemma type_test_ternary :
    ⊢ typed_function impl_test_ternary type_of_test_ternary.
  Proof.
    Open Scope printing_sugar.
    start_function "test_ternary" ([]) => local_local.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_ternary" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_ternary".
  Qed.
End proof_test_ternary.
