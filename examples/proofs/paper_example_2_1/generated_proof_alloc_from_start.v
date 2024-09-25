From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_1 Require Import generated_code.
From refinedc.examples.paper_example_2_1 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section proof_alloc_from_start.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc_from_start]. *)
  Lemma type_alloc_from_start :
    ⊢ typed_function impl_alloc_from_start type_of_alloc_from_start.
  Proof.
    Local Open Scope printing_sugar.
    start_function "alloc_from_start" ([[a n] p]) => arg_d arg_sz local_res.
    prepare_parameters (a n p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc_from_start" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "alloc_from_start".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "alloc_from_start".
  Qed.
End proof_alloc_from_start.
