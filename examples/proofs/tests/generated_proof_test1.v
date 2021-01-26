From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test1]. *)
  Lemma type_test1 :
    ⊢ typed_function impl_test1 type_of_test1.
  Proof.
    Open Scope printing_sugar.
    start_function "test1" ([]) => local_i local_c local_s local_ll local_l.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test1".
  Qed.
End proof_test1.