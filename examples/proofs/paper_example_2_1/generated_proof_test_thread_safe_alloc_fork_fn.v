From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_1 Require Import generated_code.
From refinedc.examples.paper_example_2_1 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section proof_test_thread_safe_alloc_fork_fn.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [test_thread_safe_alloc_fork_fn]. *)
  Lemma type_test_thread_safe_alloc_fork_fn (global_thread_safe_alloc : loc) :
    global_thread_safe_alloc ◁ᵥ global_thread_safe_alloc @ function_ptr type_of_thread_safe_alloc -∗
    typed_function (impl_test_thread_safe_alloc_fork_fn global_thread_safe_alloc) type_of_test_thread_safe_alloc_fork_fn.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_thread_safe_alloc_fork_fn" ([]) => arg_num local_num_int.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_thread_safe_alloc_fork_fn" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_thread_safe_alloc_fork_fn".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_thread_safe_alloc_fork_fn".
  Qed.
End proof_test_thread_safe_alloc_fork_fn.
