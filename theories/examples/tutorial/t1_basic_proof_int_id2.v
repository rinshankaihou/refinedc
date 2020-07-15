From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t1_basic_code.
From refinedc.examples.tutorial Require Import t1_basic_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t1_basic.c]. *)
Section proof_int_id2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [int_id2]. *)
  Lemma type_int_id2 :
    ⊢ typed_function impl_int_id2 type_of_int_id2.
  Proof.
    start_function "int_id2" (n) => arg_a.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "int_id2" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "int_id2".
  Qed.
End proof_int_id2.
