From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_unreachable.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [unreachable]. *)
  Lemma type_unreachable :
    ⊢ typed_function impl_unreachable type_of_unreachable.
  Proof.
    Open Scope printing_sugar.
    start_function "unreachable" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "unreachable" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "unreachable".
  Qed.
End proof_unreachable.
