From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import code.
From refinedc.examples.reverse Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init]. *)
  Lemma type_init :
    ⊢ typed_function impl_init type_of_init.
  Proof.
    start_function "init" ([]).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init".
  Qed.
End proof_init.
