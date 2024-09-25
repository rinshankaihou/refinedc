From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_tag.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tag]. *)
  Lemma type_tag (global_copy_alloc_id : loc) :
    global_copy_alloc_id ◁ᵥ global_copy_alloc_id @ inline_function_ptr impl_copy_alloc_id -∗
    typed_function (impl_tag global_copy_alloc_id) type_of_tag.
  Proof.
    Local Open Scope printing_sugar.
    start_function "tag" ([[r t] ty]) => arg_p arg_t local_i local_new_i local_q.
    prepare_parameters (r t ty).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tag" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: rewrite Z_lor_land_not; solve_goal.
    all: print_sidecondition_goal "tag".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "tag".
  Qed.
End proof_tag.
