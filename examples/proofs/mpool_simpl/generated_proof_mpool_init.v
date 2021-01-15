From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From refinedc.examples.mpool_simpl Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_mpool_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [mpool_init]. *)
  Lemma type_mpool_init :
    ⊢ typed_function impl_mpool_init type_of_mpool_init.
  Proof.
    Open Scope printing_sugar.
    start_function "mpool_init" (p) => arg_p.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "mpool_init" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "mpool_init".
  Qed.
End proof_mpool_init.
