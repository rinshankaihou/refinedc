From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From refinedc.examples.mpool_simpl Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_mpool_put.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [mpool_put]. *)
  Lemma type_mpool_put :
    ⊢ typed_function impl_mpool_put type_of_mpool_put.
  Proof.
    Open Scope printing_sugar.
    start_function "mpool_put" ([p n]) => arg_p arg_ptr local_e.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_put" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_put".
  Qed.
End proof_mpool_put.
