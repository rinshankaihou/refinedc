From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import code.
From refinedc.examples.queue Require Import spec.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_init_queue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_queue]. *)
  Lemma type_init_queue (alloc : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_init_queue alloc) type_of_init_queue.
  Proof.
    start_function "init_queue" ([]) => local_queue.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_queue" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "init_queue".
  Qed.
End proof_init_queue.
