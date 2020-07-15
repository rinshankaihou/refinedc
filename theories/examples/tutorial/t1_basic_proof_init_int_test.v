From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t1_basic_code.
From refinedc.examples.tutorial Require Import t1_basic_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t1_basic.c]. *)
Section proof_init_int_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int_test]. *)
  Lemma type_init_int_test (init_int : loc) :
    init_int ◁ᵥ init_int @ function_ptr type_of_init_int -∗
    typed_function (impl_init_int_test init_int) type_of_init_int_test.
  Proof.
    start_function "init_int_test" (p) => arg_out local_i.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_int_test" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init_int_test".
  Qed.
End proof_init_int_test.
