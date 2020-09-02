From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t5_main_code.
From refinedc.examples.tutorial Require Import t5_main_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
From refinedc.examples.latch Require Import latch_def.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t5_main.c]. *)
Section proof_main2.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [main2]. *)
  Lemma type_main2 (initialized test latch_wait : loc) :
    global_locs !! "initialized" = Some initialized →
    global_initialized_types !! "initialized" = Some (GT () (λ '(), (latch (alloc_initialized)) : type)) →
    test ◁ᵥ test @ function_ptr type_of_test -∗
    latch_wait ◁ᵥ latch_wait @ function_ptr type_of_latch_wait -∗
    typed_function (impl_main2 initialized test latch_wait) type_of_main2.
  Proof.
    start_function "main2" ([]).
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main2" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "main2".
  Qed.
End proof_main2.
