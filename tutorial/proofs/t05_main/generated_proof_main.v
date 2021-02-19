From refinedc.typing Require Import typing.
From refinedc.tutorial.t05_main Require Import generated_code.
From refinedc.tutorial.t05_main Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (global_allocator_data global_initialized global_free global_init_alloc global_latch_release global_test : loc) :
    global_locs !! "allocator_data" = Some global_allocator_data →
    global_locs !! "initialized" = Some global_initialized →
    global_initialized_types !! "initialized" = Some (GT () (λ '(), ((alloc_initialized) @ (latch)) : type)%I) →
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_init_alloc ◁ᵥ global_init_alloc @ function_ptr type_of_init_alloc -∗
    global_latch_release ◁ᵥ global_latch_release @ function_ptr type_of_latch_release -∗
    global_test ◁ᵥ global_test @ function_ptr type_of_test -∗
    typed_function (impl_main global_allocator_data global_initialized global_free global_init_alloc global_latch_release global_test) type_of_main.
  Proof.
    Open Scope printing_sugar.
    start_function "main" ([]).
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
