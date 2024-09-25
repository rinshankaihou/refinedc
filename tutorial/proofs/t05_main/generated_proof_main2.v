From refinedc.typing Require Import typing.
From refinedc.tutorial.t05_main Require Import generated_code.
From refinedc.tutorial.t05_main Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section proof_main2.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [main2]. *)
  Lemma type_main2 (global_initialized global_latch_wait global_test : loc) :
    global_locs !! "initialized" = Some global_initialized →
    global_initialized_types !! "initialized" = Some (GT (()) (λ '(), ((talloc_initialized) @ (latch)) : type)%I) →
    global_latch_wait ◁ᵥ global_latch_wait @ function_ptr type_of_latch_wait -∗
    global_test ◁ᵥ global_test @ function_ptr type_of_test -∗
    typed_function (impl_main2 global_initialized global_latch_wait global_test) type_of_main2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "main2" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "main2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "main2".
  Qed.
End proof_main2.
