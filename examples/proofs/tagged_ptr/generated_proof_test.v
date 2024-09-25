From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_tag global_tag_of global_untag : loc) :
    global_tag ◁ᵥ global_tag @ function_ptr type_of_tag -∗
    global_tag_of ◁ᵥ global_tag_of @ function_ptr type_of_tag_of -∗
    global_untag ◁ᵥ global_untag @ function_ptr type_of_untag -∗
    typed_function (impl_test global_tag global_tag_of global_untag) type_of_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test" ([]) => local_tp local_x local_px.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test".
  Qed.
End proof_test.
