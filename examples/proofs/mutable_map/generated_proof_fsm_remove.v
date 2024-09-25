From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_remove.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fsm_remove]. *)
  Lemma type_fsm_remove (global_fsm_probe : loc) :
    global_fsm_probe ◁ᵥ global_fsm_probe @ function_ptr type_of_fsm_probe -∗
    typed_function (impl_fsm_remove global_fsm_probe) type_of_fsm_remove.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fsm_remove" ([[[[m mp] items] count] key]) => arg_m arg_key local_item local_removed local_slot_idx.
    prepare_parameters (m mp items count key).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_remove" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: fsm_invariant_delete; solve_goal.
    all: try by erewrite length_filter_insert => //; solve_goal.
    all: try by eexists _; solve_goal.
    all: print_sidecondition_goal "fsm_remove".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fsm_remove".
  Qed.
End proof_fsm_remove.
