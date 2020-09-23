From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import code.
From refinedc.tutorial.t01_basic Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_int_id.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_id]. *)
  Lemma type_int_id :
    ⊢ typed_function impl_int_id type_of_int_id.
  Proof.
    start_function "int_id" ([]) => arg_a.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_id" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "int_id".
  Qed.
End proof_int_id.
