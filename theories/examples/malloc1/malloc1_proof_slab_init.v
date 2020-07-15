From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import malloc1_code.
From refinedc.examples.malloc1 Require Import malloc1_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/malloc1/malloc1.c]. *)
Section proof_slab_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_init]. *)
  Lemma type_slab_init :
    ⊢ typed_function impl_slab_init type_of_slab_init.
  Proof.
    start_function "slab_init" ([[[p chunk_p] n] entry_size]) => arg_s arg_p arg_chunksize arg_entry_size.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_init" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "slab_init".
  Qed.
End proof_slab_init.
