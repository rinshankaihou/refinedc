From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From refinedc.examples.malloc1 Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section proof_slab_free.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_free]. *)
  Lemma type_slab_free :
    ⊢ typed_function impl_slab_free type_of_slab_free.
  Proof.
    Local Open Scope printing_sugar.
    start_function "slab_free" ([[[p fp] n] entry_size]) => arg_s arg_x local_f.
    prepare_parameters (p fp n entry_size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_free" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "slab_free".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "slab_free".
  Qed.
End proof_slab_free.
