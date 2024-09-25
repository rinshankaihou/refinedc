From refinedc.typing Require Import typing.
From refinedc.examples.scheduler.src.fdsched Require Import generated_code.
From refinedc.examples.scheduler.src.fdsched Require Import generated_spec.
From refinedc.examples.scheduler.src.fdsched Require Import message_extra.
From caesium Require Import builtins_specs.
From refinedc.examples.scheduler.src.fdsched Require Import priority_extra.
From refinedc.examples.scheduler.src.fdsched Require Import scheduler_extra.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
From refinedc.typing Require Import malloc.
From refinedc.examples.scheduler.src.fdsched Require Import fdsched_extra.
Set Default Proof Using "Type".

(* Generated from [examples/scheduler/src/fdsched.c]. *)
Section proof_highest_pending_priority.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [highest_pending_priority]. *)
  Lemma type_highest_pending_priority (global___builtin_ffsll : loc) :
    global___builtin_ffsll ◁ᵥ global___builtin_ffsll @ function_ptr type_of___builtin_ffsll -∗
    typed_function (impl_highest_pending_priority global___builtin_ffsll) type_of_highest_pending_priority.
  Proof.
    Local Open Scope printing_sugar.
    start_function "highest_pending_priority" ([p bm]) => arg_bm local_i local_first_bit local_offset.
    prepare_parameters (p bm).
    split_blocks ((
      <[ "#1" :=
        ∃ lvl : Z,
        arg_bm ◁ₗ (p @ (&own (bm @ (prio_bitmap_t)))) ∗
        local_first_bit ◁ₗ uninit (it_layout i32) ∗
        local_i ◁ₗ (lvl @ (int (i32))) ∗
        local_offset ◁ₗ ((lvl * 64 - 1) @ (int (i32))) ∗
        ⌜0 <= lvl <= 4⌝ ∗
        ⌜forall (j : Z), 0 <= j < lvl * 64 -> bm !! (Z.to_nat j) = Some false⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "highest_pending_priority" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "highest_pending_priority" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + have := Z_least_significant_one_lower_bound y. solve_goal.
    + have := encode_prio_bitmap_least_significant_one_bound bm lvl y. solve_goal.
    + rewrite (highest_pending_priority_found _ y lvl); solve_goal.
    + apply (highest_pending_priority_not_in_element _ lvl y); solve_goal.
    + symmetry; apply (highest_pending_priority_not_found _ lvl); solve_goal.
    all: print_sidecondition_goal "highest_pending_priority".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "highest_pending_priority".
  Qed.
End proof_highest_pending_priority.
