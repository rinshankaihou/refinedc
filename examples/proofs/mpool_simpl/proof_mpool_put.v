From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import code.
From refinedc.examples.mpool_simpl Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_mpool_put.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [mpool_put]. *)
  Lemma type_mpool_put :
    ⊢ typed_function impl_mpool_put type_of_mpool_put.
  Proof.
    start_function "mpool_put" ([p n]) => arg_p arg_ptr local_e.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_put" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "mpool_put".
  Qed.
End proof_mpool_put.
