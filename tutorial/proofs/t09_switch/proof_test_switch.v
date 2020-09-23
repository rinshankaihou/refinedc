From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import code.
From refinedc.tutorial.t09_switch Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section proof_test_switch.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_switch]. *)
  Lemma type_test_switch :
    ⊢ typed_function impl_test_switch type_of_test_switch.
  Proof.
    start_function "test_switch" (i) => arg_i local_o.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_switch" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test_switch".
  Qed.
End proof_test_switch.
