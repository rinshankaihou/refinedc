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
  Lemma type_main (global_allocator_data global_initialized global_init_talloc global_latch_release global_test global_tfree : loc) :
    global_locs !! "allocator_data" = Some global_allocator_data →
    global_locs !! "initialized" = Some global_initialized →
    global_initialized_types !! "initialized" = Some (GT (()) (λ '(), ((talloc_initialized) @ (latch)) : type)%I) →
    global_init_talloc ◁ᵥ global_init_talloc @ function_ptr type_of_init_talloc -∗
    global_latch_release ◁ᵥ global_latch_release @ function_ptr type_of_latch_release -∗
    global_test ◁ᵥ global_test @ function_ptr type_of_test -∗
    global_tfree ◁ᵥ global_tfree @ function_ptr type_of_tfree -∗
    typed_function (impl_main global_allocator_data global_initialized global_init_talloc global_latch_release global_test global_tfree) type_of_main.
  Proof.
    Local Open Scope printing_sugar.
    start_function "main" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "main".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "main".
  Qed.
End proof_main.
