From refinedc.typing Require Import typing.
From refinedc.tutorial.t05_main Require Import code.
From refinedc.tutorial.t05_main Require Import spec.
From refinedc.examples.latch Require Import latch_def.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (initialized allocator_data latch_release test free init_alloc : loc) :
    global_locs !! "initialized" = Some initialized →
    global_locs !! "allocator_data" = Some allocator_data →
    global_initialized_types !! "initialized" = Some (GT () (λ '(), (latch (alloc_initialized)) : type)) →
    latch_release ◁ᵥ latch_release @ function_ptr type_of_latch_release -∗
    test ◁ᵥ test @ function_ptr type_of_test -∗
    free ◁ᵥ free @ function_ptr type_of_free -∗
    init_alloc ◁ᵥ init_alloc @ function_ptr type_of_init_alloc -∗
    typed_function (impl_main initialized allocator_data latch_release test free init_alloc) type_of_main.
  Proof.
    start_function "main" ([]).
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
