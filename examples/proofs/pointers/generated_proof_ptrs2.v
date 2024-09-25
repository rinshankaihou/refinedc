From refinedc.typing Require Import typing.
From refinedc.examples.pointers Require Import generated_code.
From refinedc.examples.pointers Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section proof_ptrs2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptrs2]. *)
  Lemma type_ptrs2 :
    ⊢ typed_function impl_ptrs2 type_of_ptrs2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "ptrs2" (p) => arg_b arg_p local_p1.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptrs2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "ptrs2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "ptrs2".
  Qed.
End proof_ptrs2.
