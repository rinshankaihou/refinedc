From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_ptrs.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptrs]. *)
  Lemma type_ptrs :
    ⊢ typed_function impl_ptrs type_of_ptrs.
  Proof.
    start_function "ptrs" (p) => arg_b arg_p local_p1 local_p2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptrs" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "ptrs".
  Qed.
End proof_ptrs.
