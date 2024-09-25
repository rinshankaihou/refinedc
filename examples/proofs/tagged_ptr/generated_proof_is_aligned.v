From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_is_aligned.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [is_aligned]. *)
  Lemma type_is_aligned :
    ⊢ typed_function impl_is_aligned type_of_is_aligned.
  Proof.
    Local Open Scope printing_sugar.
    start_function "is_aligned" ([l n]) => arg_p local_i.
    prepare_parameters (l n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "is_aligned" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: unfold_aligned_to; split; solve_goal.
    all: print_sidecondition_goal "is_aligned".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "is_aligned".
  Qed.
End proof_is_aligned.
