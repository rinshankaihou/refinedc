From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t2_pointers_code.
From refinedc.examples.tutorial Require Import t2_pointers_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t2_pointers.c]. *)
Section proof_ptrs.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptrs]. *)
  Lemma type_ptrs :
    ⊢ typed_function impl_ptrs type_of_ptrs.
  Proof.
    start_function "ptrs" (p) => arg_b arg_p local_p1 local_p2.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptrs" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "ptrs".
  Qed.
End proof_ptrs.
