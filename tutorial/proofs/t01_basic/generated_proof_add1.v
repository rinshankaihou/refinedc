From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_add1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [add1]. *)
  Lemma type_add1 :
    ⊢ typed_function impl_add1 type_of_add1.
  Proof.
    start_function "add1" (n) => arg_a.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "add1" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "add1".
  Qed.
End proof_add1.
