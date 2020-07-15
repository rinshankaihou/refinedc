From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t8_tree_code.
From refinedc.examples.tutorial Require Import t8_tree_spec.
From refinedc.examples.tutorial Require Import t8_tree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t8_tree.c]. *)
Section proof_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [empty]. *)
  Lemma type_empty :
    ⊢ typed_function impl_empty type_of_empty.
  Proof.
    start_function "empty" ([]).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "empty" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "empty".
  Qed.
End proof_empty.
