From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo_alloc_full Require Import generated_code.
From refinedc.examples.talk_demo_alloc_full Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc_full.c]. *)
Section proof_alloc_2_alt.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc_2_alt]. *)
  Lemma type_alloc_2_alt :
    ⊢ typed_function impl_alloc_2_alt type_of_alloc_2_alt.
  Proof.
    Local Open Scope printing_sugar.
    start_function "alloc_2_alt" (p) => arg_d arg_sz.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc_2_alt" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "alloc_2_alt".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "alloc_2_alt".
  Qed.
End proof_alloc_2_alt.
