From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_ptrs2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptrs2]. *)
  Lemma type_ptrs2 :
    ⊢ typed_function impl_ptrs2 type_of_ptrs2.
  Proof.
    start_function "ptrs2" (p) => arg_b arg_p local_p1.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptrs2" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "ptrs2".
  Qed.
End proof_ptrs2.
