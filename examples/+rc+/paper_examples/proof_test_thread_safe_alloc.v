From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import code.
From refinedc.examples.paper_examples Require Import spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section proof_test_thread_safe_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [test_thread_safe_alloc]. *)
  Lemma type_test_thread_safe_alloc (param thread_safe_alloc fork test_thread_safe_alloc_fork_fn : loc) :
    global_locs !! "param" = Some param →
    thread_safe_alloc ◁ᵥ thread_safe_alloc @ function_ptr type_of_thread_safe_alloc -∗
    fork ◁ᵥ fork @ function_ptr type_of_fork -∗
    test_thread_safe_alloc_fork_fn ◁ᵥ test_thread_safe_alloc_fork_fn @ function_ptr type_of_test_thread_safe_alloc_fork_fn -∗
    typed_function (impl_test_thread_safe_alloc param thread_safe_alloc fork test_thread_safe_alloc_fork_fn) type_of_test_thread_safe_alloc.
  Proof.
    start_function "test_thread_safe_alloc" (lid).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_thread_safe_alloc" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "test_thread_safe_alloc".
  Qed.
End proof_test_thread_safe_alloc.
