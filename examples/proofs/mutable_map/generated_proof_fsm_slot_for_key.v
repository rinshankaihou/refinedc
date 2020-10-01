From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_slot_for_key.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [fsm_slot_for_key]. *)
  Lemma type_fsm_slot_for_key :
    ⊢ typed_function impl_fsm_slot_for_key type_of_fsm_slot_for_key.
  Proof.
    start_function "fsm_slot_for_key" ([len key]) => arg_len arg_key.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_slot_for_key" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: slot_for_key_ref_unfold_rem; solve_goal.
    all: print_sidecondition_goal "fsm_slot_for_key".
  Qed.
End proof_fsm_slot_for_key.
