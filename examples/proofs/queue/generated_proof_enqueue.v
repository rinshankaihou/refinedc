From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_enqueue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [enqueue]. *)
  Lemma type_enqueue (alloc : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_enqueue alloc) type_of_enqueue.
  Proof.
    start_function "enqueue" ([[p tys] ty]) => arg_q arg_v local_elem.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "enqueue" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "enqueue".
  Qed.
End proof_enqueue.
