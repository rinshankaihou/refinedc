From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t1_basic_code.
From refinedc.examples.tutorial Require Import t1_basic_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t1_basic.c]. *)
Section proof_struct_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [struct_test]. *)
  Lemma type_struct_test :
    ⊢ typed_function impl_struct_test type_of_struct_test.
  Proof.
    start_function "struct_test" (p) => arg_out.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "struct_test" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "struct_test".
  Qed.
End proof_struct_test.
