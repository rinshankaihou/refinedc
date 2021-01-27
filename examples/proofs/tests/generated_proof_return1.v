From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_return1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [return1]. *)
  Lemma type_return1 :
    ⊢ typed_function impl_return1 type_of_return1.
  Proof.
    Open Scope printing_sugar.
    start_function "return1" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "return1" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "return1".
  Qed.
End proof_return1.
