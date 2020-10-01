From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import generated_code.
From refinedc.examples.paper_examples Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section proof_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc]. *)
  Lemma type_alloc :
    ⊢ typed_function impl_alloc type_of_alloc.
  Proof.
    start_function "alloc" ([[nlen nsize] p]) => arg_d arg_size.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "alloc".
  Qed.
End proof_alloc.
