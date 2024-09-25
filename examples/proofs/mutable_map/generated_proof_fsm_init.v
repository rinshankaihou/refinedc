From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_fsm_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fsm_init]. *)
  Lemma type_fsm_init (global_xmalloc : loc) :
    global_xmalloc ◁ᵥ global_xmalloc @ function_ptr type_of_xmalloc -∗
    typed_function (impl_fsm_init global_xmalloc) type_of_fsm_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fsm_init" ([m len]) => arg_m arg_len local_i local_storage.
    prepare_parameters (m len).
    split_blocks ((
      <[ "#1" :=
        ∃ i : nat,
        arg_len ◁ₗ (len @ (int (size_t))) ∗
        local_storage ◁ₗ uninit void* ∗
        local_i ◁ₗ (i @ (int (size_t))) ∗
        arg_m ◁ₗ (m @ (&own (struct (struct_fixed_size_map) [@{type} &own (malloced (ly_size struct_item * len) (array (struct_item) (replicate i Empty `at_type` item ++ replicate (len - i)%nat (uninit (struct_item))))) ; len @ (int (size_t)) ; len @ (int (size_t)) ]))) ∗
        ⌜i <= len⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_init" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fsm_init" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: fsm_invariant_init; solve_goal.
    all: try by apply/list_subequiv_split; solve_goal.
    all: try by rewrite length_filter_replicate_True; solve_goal.
    all: try by rewrite !replicate_O; solve_goal.
    all: print_sidecondition_goal "fsm_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fsm_init".
  Qed.
End proof_fsm_init.
