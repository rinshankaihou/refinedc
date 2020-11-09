From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From refinedc.examples.mpool_simpl Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_mpool_get.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [mpool_get]. *)
  Lemma type_mpool_get :
    ⊢ typed_function impl_mpool_get type_of_mpool_get.
  Proof.
    start_function "mpool_get" ([p n]) => arg_p local_entry.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_get" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_get".
  Qed.
End proof_mpool_get.
