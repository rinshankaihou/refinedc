From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_dequeue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [dequeue]. *)
  Lemma type_dequeue (free : loc) :
    free ◁ᵥ free @ function_ptr type_of_free -∗
    typed_function (impl_dequeue free) type_of_dequeue.
  Proof.
    start_function "dequeue" ([p tys]) => arg_q local_elem local_ret.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "dequeue" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "dequeue".
  Qed.
End proof_dequeue.
