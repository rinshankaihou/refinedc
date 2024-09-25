From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_slot_for_key.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fsm_slot_for_key]. *)
  Lemma type_fsm_slot_for_key :
    ⊢ typed_function impl_fsm_slot_for_key type_of_fsm_slot_for_key.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fsm_slot_for_key" ([len key]) => arg_len arg_key.
    prepare_parameters (len key).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_slot_for_key" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: slot_for_key_ref_unfold_rem; solve_goal.
    all: print_sidecondition_goal "fsm_slot_for_key".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fsm_slot_for_key".
  Qed.
End proof_fsm_slot_for_key.
