From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_realloc_if_necessary.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fsm_realloc_if_necessary]. *)
  Lemma type_fsm_realloc_if_necessary (global_compute_min_count global_free global_fsm_init global_fsm_insert : loc) :
    global_compute_min_count ◁ᵥ global_compute_min_count @ function_ptr type_of_compute_min_count -∗
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_fsm_init ◁ᵥ global_fsm_init @ function_ptr type_of_fsm_init -∗
    global_fsm_insert ◁ᵥ global_fsm_insert @ function_ptr type_of_fsm_insert -∗
    typed_function (impl_fsm_realloc_if_necessary global_compute_min_count global_free global_fsm_init global_fsm_insert) type_of_fsm_realloc_if_necessary.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fsm_realloc_if_necessary" ([[[m items] count] mp]) => arg_m local_i local_m2 local_new_len.
    prepare_parameters (m items count mp).
    split_blocks ((
      <[ "#3" :=
        ∃ i : nat,
        ∃ items2 : list item_ref,
        ∃ count2 : nat,
        local_new_len ◁ₗ uninit (it_layout size_t) ∗
        local_i ◁ₗ (i @ (int (size_t))) ∗
        arg_m ◁ₗ (m @ (&own (struct (struct_fixed_size_map) [@{type} &own (malloced (ly_size struct_item * length items) (array (struct_item) (replicate i (uninit struct_item) ++ (drop i items `at_type` item)))) ; int (size_t) ; (length items) @ (int (size_t)) ]))) ∗
        local_m2 ◁ₗ ((fsm_copy_entries items i, items2, count2) @ (fixed_size_map)) ∗
        ⌜count + length items - i < count2⌝ ∗
        ⌜i <= length items⌝ ∗
        ⌜0 < count⌝ ∗
        ⌜length items * 2 <= length items2⌝ ∗
        ⌜fsm_invariant mp items⌝ ∗
        ⌜struct_item.(ly_size) * length items ≤ max_int size_t⌝
    ]> $
      <[ "#11" :=
        arg_m ◁ₗ (m @ (&own ((mp, items, count) @ (fixed_size_map)))) ∗
        local_i ◁ₗ uninit (it_layout size_t) ∗
        local_m2 ◁ₗ uninit (layout_of struct_fixed_size_map) ∗
        local_new_len ◁ₗ uninit (it_layout size_t)
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#3".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_realloc_if_necessary" "#11".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by eexists (length items); split_and?; rewrite ?drop_ge; solve_goal.
    all: try match goal with | H : fsm_invariant ?mp2 ?items2 |- fsm_invariant ?mp1 ?items1 => have ->: mp1 = mp2; [|done] end.
    all: try by apply: fsm_copy_entries_not_add; solve_goal.
    all: try by apply: fsm_copy_entries_add; solve_goal.
    all: try by apply: fsm_copy_entries_id; solve_goal.
    all: try by apply list_subequiv_split; [solve_goal|]; normalize_and_simpl_goal; try solve_goal; f_equal; solve_goal.
    all: print_sidecondition_goal "fsm_realloc_if_necessary".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fsm_realloc_if_necessary".
  Qed.
End proof_fsm_realloc_if_necessary.
