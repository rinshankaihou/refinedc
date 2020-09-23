From refinedc.typing Require Import typing.
From refinedc.examples.mpool_simpl Require Import code.
From refinedc.examples.mpool_simpl Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (e1 e2 mpool_get mpool_init mpool_put : loc) :
    global_locs !! "e1" = Some e1 →
    global_locs !! "e2" = Some e2 →
    mpool_get ◁ᵥ mpool_get @ function_ptr type_of_mpool_get -∗
    mpool_init ◁ᵥ mpool_init @ function_ptr type_of_mpool_init -∗
    mpool_put ◁ᵥ mpool_put @ function_ptr type_of_mpool_put -∗
    typed_function (impl_main e1 e2 mpool_get mpool_init mpool_put) type_of_main.
  Proof.
    start_function "main" ([]) => local_p1 local_p2 local_p.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "main".
  Qed.
End proof_main.
