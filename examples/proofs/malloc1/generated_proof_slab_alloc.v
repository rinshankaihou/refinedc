From refinedc.typing Require Import typing.
From refinedc.examples.malloc1 Require Import generated_code.
From refinedc.examples.malloc1 Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/malloc1.c]. *)
Section proof_slab_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [slab_alloc]. *)
  Lemma type_slab_alloc :
    ⊢ typed_function impl_slab_alloc type_of_slab_alloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "slab_alloc" ([[p n] entry_size]) => arg_s local_r local_f.
    prepare_parameters (p n entry_size).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "slab_alloc" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: has_layout_loc_trans'; solve_goal.
    all: print_sidecondition_goal "slab_alloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "slab_alloc".
  Qed.
End proof_slab_alloc.
