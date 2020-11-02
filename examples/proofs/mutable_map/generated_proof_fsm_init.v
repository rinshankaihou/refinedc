From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_init.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [fsm_init]. *)
  Lemma type_fsm_init (alloc_array : loc) :
    alloc_array ◁ᵥ alloc_array @ function_ptr type_of_alloc_array -∗
    typed_function (impl_fsm_init alloc_array) type_of_fsm_init.
  Proof.
    start_function "fsm_init" ([m len]) => arg_m arg_len local_i local_storage.
    split_blocks ((
      <[ "#1" :=
        ∃ i : nat,
        arg_len ◁ₗ (len @ (int (size_t))) ∗
        local_storage ◁ₗ uninit LPtr ∗
        local_i ◁ₗ (i @ (int (size_t))) ∗
        arg_m ◁ₗ (m @ (&own (struct (struct_fixed_size_map) [@{type} &own (array (struct_item) (replicate i Empty `at_type` item ++ replicate (len - i)%nat (uninit (struct_item)))) ; len @ (int (size_t)) ; len @ (int (size_t)) ]))) ∗
        ⌜i <= len⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_init" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_init" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: fsm_invariant_init; solve_goal.
    all: try by apply/list_subequiv_split; solve_goal.
    all: try by rewrite length_filter_replicate_True; solve_goal.
    all: try by rewrite !replicate_O; solve_goal.
    all: print_sidecondition_goal "fsm_init".
  Qed.
End proof_fsm_init.
