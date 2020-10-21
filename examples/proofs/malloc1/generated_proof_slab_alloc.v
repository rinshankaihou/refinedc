From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From refinedc.examples.malloc1 Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section proof_slab_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_alloc]. *)
  Lemma type_slab_alloc :
    ⊢ typed_function impl_slab_alloc type_of_slab_alloc.
  Proof.
    start_function "slab_alloc" ([[p n] entry_size]) => arg_s local_r local_f.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_alloc" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "slab_alloc".
  Qed.
End proof_slab_alloc.
