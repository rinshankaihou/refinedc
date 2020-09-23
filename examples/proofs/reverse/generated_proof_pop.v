From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_pop.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [pop]. *)
  Lemma type_pop :
    ⊢ typed_function impl_pop type_of_pop.
  Proof.
    start_function "pop" ([l p]) => arg_p local_ret.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "pop" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "pop".
  Qed.
End proof_pop.
