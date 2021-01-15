From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From refinedc.examples.btree Require Import generated_spec.
From refinedc.examples.btree Require Import btree_extra.
From refinedc.examples.btree Require Import btree_learn.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section proof_new_btree.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [new_btree]. *)
  Lemma type_new_btree (global_alloc : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_new_btree global_alloc) type_of_new_btree.
  Proof.
    Open Scope printing_sugar.
    start_function "new_btree" ([]) => local_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "new_btree" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "new_btree".
  Qed.
End proof_new_btree.
