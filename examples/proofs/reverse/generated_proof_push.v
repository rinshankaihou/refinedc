From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_push.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [push]. *)
  Lemma type_push :
    ⊢ typed_function impl_push type_of_push.
  Proof.
    Open Scope printing_sugar.
    start_function "push" ([l ty]) => arg_p arg_e arg_node.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "push" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "push".
  Qed.
End proof_push.
