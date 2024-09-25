From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From refinedc.examples.malloc1 Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section proof_slab_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_init]. *)
  Lemma type_slab_init :
    ⊢ typed_function impl_slab_init type_of_slab_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "slab_init" ([[[p chunk_p] n] entry_size]) => arg_s arg_p arg_chunksize arg_entry_size.
    prepare_parameters (p chunk_p n entry_size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_init" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "slab_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "slab_init".
  Qed.
End proof_slab_init.
