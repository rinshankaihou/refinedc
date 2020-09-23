From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import code.
From refinedc.examples.reverse Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_push.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [push]. *)
  Lemma type_push :
    ⊢ typed_function impl_push type_of_push.
  Proof.
    start_function "push" ([l ty]) => arg_p arg_e arg_node.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "push" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "push".
  Qed.
End proof_push.
