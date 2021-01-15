From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import generated_code.
From refinedc.examples.mpool_simpl Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (global_e1 global_e2 global_mpool_get global_mpool_init global_mpool_put : loc) :
    global_locs !! "e1" = Some global_e1 →
    global_locs !! "e2" = Some global_e2 →
    global_mpool_get ◁ᵥ global_mpool_get @ function_ptr type_of_mpool_get -∗
    global_mpool_init ◁ᵥ global_mpool_init @ function_ptr type_of_mpool_init -∗
    global_mpool_put ◁ᵥ global_mpool_put @ function_ptr type_of_mpool_put -∗
    typed_function (impl_main global_e1 global_e2 global_mpool_get global_mpool_init global_mpool_put) type_of_main.
  Proof.
    Open Scope printing_sugar.
    start_function "main" ([]) => local_p1 local_p2 local_p.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "main".
  Qed.
End proof_main.
