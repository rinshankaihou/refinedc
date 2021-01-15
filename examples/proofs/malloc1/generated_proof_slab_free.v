From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From refinedc.examples.malloc1 Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section proof_slab_free.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_free]. *)
  Lemma type_slab_free :
    ⊢ typed_function impl_slab_free type_of_slab_free.
  Proof.
    Open Scope printing_sugar.
    start_function "slab_free" ([[[p fp] n] entry_size]) => arg_s arg_x local_f.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_free" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "slab_free".
  Qed.
End proof_slab_free.
