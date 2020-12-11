From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_init_queue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_queue]. *)
  Lemma type_init_queue (global_alloc : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_init_queue global_alloc) type_of_init_queue.
  Proof.
    start_function "init_queue" ([]) => local_queue.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_queue" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_queue".
  Qed.
End proof_init_queue.
