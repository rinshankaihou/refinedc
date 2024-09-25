From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo_alloc Require Import generated_code.
From refinedc.examples.talk_demo_alloc Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc.c]. *)
Section proof_alloc.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc]. *)
  Lemma type_alloc :
    ⊢ typed_function impl_alloc type_of_alloc.
  Proof.
    Local Open Scope printing_sugar.
    start_function "alloc" ([[p a] n]) => arg_d arg_sz.
    prepare_parameters (p a n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "alloc".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "alloc".
  Qed.
End proof_alloc.
