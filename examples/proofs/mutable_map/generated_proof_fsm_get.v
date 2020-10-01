From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_get.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [fsm_get]. *)
  Lemma type_fsm_get (fsm_probe : loc) :
    fsm_probe ◁ᵥ fsm_probe @ function_ptr type_of_fsm_probe -∗
    typed_function (impl_fsm_get fsm_probe) type_of_fsm_get.
  Proof.
    start_function "fsm_get" ([[[[m mp] items] count] key]) => arg_m arg_key local_item local_slot_idx.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_get" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: fsm_invariant_alter; solve_goal.
    all: try by erewrite length_filter_insert => //; solve_goal.
    all: print_sidecondition_goal "fsm_get".
  Qed.
End proof_fsm_get.
