From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import code.
From refinedc.tutorial.t06_struct Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_blue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [blue]. *)
  Lemma type_blue :
    ⊢ typed_function impl_blue type_of_blue.
  Proof.
    start_function "blue" (b) => arg_b local_c.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "blue" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "blue".
  Qed.
End proof_blue.
