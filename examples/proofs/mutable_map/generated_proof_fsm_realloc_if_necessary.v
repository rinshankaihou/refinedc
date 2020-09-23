From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_realloc_if_necessary.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [fsm_realloc_if_necessary]. *)
  Lemma type_fsm_realloc_if_necessary (compute_min_count free_array fsm_init fsm_insert : loc) :
    compute_min_count ◁ᵥ compute_min_count @ function_ptr type_of_compute_min_count -∗
    free_array ◁ᵥ free_array @ function_ptr type_of_free_array -∗
    fsm_init ◁ᵥ fsm_init @ function_ptr type_of_fsm_init -∗
    fsm_insert ◁ᵥ fsm_insert @ function_ptr type_of_fsm_insert -∗
    typed_function (impl_fsm_realloc_if_necessary compute_min_count free_array fsm_init fsm_insert) type_of_fsm_realloc_if_necessary.
  Proof.
    start_function "fsm_realloc_if_necessary" ([[[m items] count] mp]) => arg_m local_i local_m2 local_new_len.
    split_blocks ((
      <[ "#3" :=
        ∃ i : nat,
        ∃ items2 : list item_ref,
        ∃ count2 : nat,
        local_new_len ◁ₗ uninit (it_layout size_t) ∗
        local_i ◁ₗ (i @ (int (size_t))) ∗
        arg_m ◁ₗ (m @ (&own (struct (struct_fixed_size_map) [@{type} &own (array (struct_item) (replicate i (uninit struct_item) ++ (drop i items `at_type` item))) ; int (size_t) ; (length items) @ (int (size_t)) ]))) ∗
        local_m2 ◁ₗ ((fsm_copy_entries items i, items2, count2) @ (fixed_size_map)) ∗
        ⌜count + length items - i < count2⌝ ∗
        ⌜i <= length items⌝ ∗
        ⌜0 < count⌝ ∗
        ⌜length items * 2 <= length items2⌝ ∗
        ⌜fsm_invariant mp items⌝ ∗
        ⌜struct_item.(ly_size) * length items < it_max size_t⌝
    ]> $
      <[ "#11" :=
        arg_m ◁ₗ (m @ (&own ((mp, items, count) @ (fixed_size_map)))) ∗
        local_i ◁ₗ uninit (it_layout size_t) ∗
        local_m2 ◁ₗ uninit (layout_of struct_fixed_size_map) ∗
        local_new_len ◁ₗ uninit (it_layout size_t)
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#3".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#11".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by eexists (length items); rewrite /shelve_hint; split_and?; rewrite ?drop_ge; solve_goal.
    all: try match goal with | H : fsm_invariant ?mp2 ?items2 |- fsm_invariant ?mp1 ?items1 => have ->: mp1 = mp2; [|done] end.
    all: try by apply: fsm_copy_entries_not_add; solve_goal.
    all: try by apply: fsm_copy_entries_add; solve_goal.
    all: try by apply: fsm_copy_entries_id; solve_goal.
    all: try (apply list_subequiv_split; [solve_goal|]).
    all: try rewrite !firstn_app !take_replicate !skipn_app !drop_replicate !replicate_length !fmap_drop !drop_drop -minus_n_n.
    all: try split; f_equal.
    all: try by f_equal; lia.
    all: try have ->:(i - (i + 1) = 0)%nat by lia.
    all: try by rewrite !firstn_O.
    all: print_sidecondition_goal "fsm_realloc_if_necessary".
  Qed.
End proof_fsm_realloc_if_necessary.
