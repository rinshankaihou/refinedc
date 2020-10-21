From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import generated_code.
From refinedc.examples.paper_examples Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section proof_test_thread_safe_alloc_fork_fn.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [test_thread_safe_alloc_fork_fn]. *)
  Lemma type_test_thread_safe_alloc_fork_fn (thread_safe_alloc : loc) :
    thread_safe_alloc ◁ᵥ thread_safe_alloc @ function_ptr type_of_thread_safe_alloc -∗
    typed_function (impl_test_thread_safe_alloc_fork_fn thread_safe_alloc) type_of_test_thread_safe_alloc_fork_fn.
  Proof.
    start_function "test_thread_safe_alloc_fork_fn" ([]) => arg_num local_num_int.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_thread_safe_alloc_fork_fn" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test_thread_safe_alloc_fork_fn".
  Qed.
End proof_test_thread_safe_alloc_fork_fn.
