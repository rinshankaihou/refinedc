From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [empty]. *)
  Lemma type_empty :
    ⊢ typed_function impl_empty type_of_empty.
  Proof.
    start_function "empty" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "empty" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "empty".
  Qed.
End proof_empty.
