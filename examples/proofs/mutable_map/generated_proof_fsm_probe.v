From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_probe.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [fsm_probe]. *)
  Lemma type_fsm_probe (global_fsm_slot_for_key : loc) :
    global_fsm_slot_for_key ◁ᵥ global_fsm_slot_for_key @ function_ptr type_of_fsm_slot_for_key -∗
    typed_function (impl_fsm_probe global_fsm_slot_for_key) type_of_fsm_probe.
  Proof.
    start_function "fsm_probe" ([[[[m mp] items] key] count]) => arg_m arg_key local_slot_idx.
    split_blocks ((
      <[ "#1" :=
        ∃ offset : nat,
        arg_m ◁ₗ (m @ (&own ((mp, items, count) @ (fixed_size_map)))) ∗
        arg_key ◁ₗ (key @ (int (size_t))) ∗
        local_slot_idx ◁ₗ ((rotate_nat_add (slot_for_key_ref key (length items)) offset (length items)) @ (int (size_t))) ∗
        ⌜probe_ref_go key (take offset (rotate (slot_for_key_ref key (length items)) items)) = None⌝ ∗
        ⌜∃ x, items !! rotate_nat_add (slot_for_key_ref key (length items)) offset (length items) = Some x⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_probe" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_probe" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: lookup_lt_is_Some_2; solve_goal.
    all: try by eexists _; split => //; apply probe_ref_take_Some; naive_solver.
    all: try by apply: probe_ref_go_next_take=> //i; intros Hi%lookup_rotate_r_Some; try lia; simplify_eq; naive_solver.
    all: print_sidecondition_goal "fsm_probe".
  Qed.
End proof_fsm_probe.
