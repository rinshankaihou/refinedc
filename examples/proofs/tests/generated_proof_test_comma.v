From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_comma.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_comma]. *)
  Lemma type_test_comma :
    ⊢ typed_function impl_test_comma type_of_test_comma.
  Proof.
    Open Scope printing_sugar.
    start_function "test_comma" ([]) => local_x.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_comma" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_comma".
  Qed.
End proof_test_comma.
