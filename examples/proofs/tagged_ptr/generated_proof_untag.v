From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_untag.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [untag]. *)
  Lemma type_untag (global_tag : loc) :
    global_tag ◁ᵥ global_tag @ function_ptr type_of_tag -∗
    typed_function (impl_untag global_tag) type_of_untag.
  Proof.
    Local Open Scope printing_sugar.
    start_function "untag" ([r ty]) => arg_p.
    prepare_parameters (r ty).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "untag" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "untag".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "untag".
  Qed.
End proof_untag.
