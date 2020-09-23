From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import code.
From refinedc.tutorial.t06_struct Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_green.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [green]. *)
  Lemma type_green :
    ⊢ typed_function impl_green type_of_green.
  Proof.
    start_function "green" (g) => arg_g.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "green" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "green".
  Qed.
End proof_green.
