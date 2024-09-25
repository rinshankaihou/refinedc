From refinedc.typing Require Import typing.
From refinedc.examples.pointers Require Import generated_code.
From refinedc.examples.pointers Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section proof_ptr_id_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptr_id_test]. *)
  Lemma type_ptr_id_test (global_ptr_id : loc) :
    global_ptr_id ◁ᵥ global_ptr_id @ function_ptr type_of_ptr_id -∗
    typed_function (impl_ptr_id_test global_ptr_id) type_of_ptr_id_test.
  Proof.
    Local Open Scope printing_sugar.
    start_function "ptr_id_test" ([]) => local_x.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptr_id_test" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "ptr_id_test".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "ptr_id_test".
  Qed.
End proof_ptr_id_test.
