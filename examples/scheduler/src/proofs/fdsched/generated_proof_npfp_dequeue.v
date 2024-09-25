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
Section proof_npfp_dequeue.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [npfp_dequeue]. *)
  Lemma type_npfp_dequeue (global_highest_pending_priority global_message_queue_empty global_message_queue_remove global_priority_level_clear global_priority_search_none_found : loc) :
    global_highest_pending_priority ◁ᵥ global_highest_pending_priority @ function_ptr type_of_highest_pending_priority -∗
    global_message_queue_empty ◁ᵥ global_message_queue_empty @ function_ptr type_of_message_queue_empty -∗
    global_message_queue_remove ◁ᵥ global_message_queue_remove @ function_ptr type_of_message_queue_remove -∗
    global_priority_level_clear ◁ᵥ global_priority_level_clear @ function_ptr type_of_priority_level_clear -∗
    global_priority_search_none_found ◁ᵥ global_priority_search_none_found @ function_ptr type_of_priority_search_none_found -∗
    typed_function (impl_npfp_dequeue global_highest_pending_priority global_message_queue_empty global_message_queue_remove global_priority_level_clear global_priority_search_none_found) type_of_npfp_dequeue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "npfp_dequeue" ([l1 sched_state]) => arg_sched local_msg local_top_prio.
    prepare_parameters (l1 sched_state).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "npfp_dequeue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all : try (rewrite /npfp_dequeue_func; solve_goal).
    + rewrite /get_highest_prio_msg /get_highest_prio_queue /get_highest_prio_level; solve_goal.
    + rewrite -(Z2Nat.id num_priorities); try solve_goal. by rewrite -(create_bitmap_length sched_state); apply find_highest_prio_length.
    + by eapply npfp_dequeue_nonempty.
    + by apply get_highest_prio_msg_is_head.
    + by eapply npfp_dequeue_no_highest_priority.
    + eapply npfp_dequeue_has_highest_pending_prio; [done..|solve_goal].
    + by eapply npfp_dequeue_create_bitmap_equiv.
    + eapply npfp_dequeue_create_bitmap_false; solve_goal.
    + by apply get_highest_prio_msg_is_head.
    + by apply npfp_dequeue_qs_equiv.
    + eapply npfp_dequeue_has_highest_pending_prio; [done..|solve_goal].
    + by eapply npfp_dequeue_create_bitmap_equiv1.
    all: print_sidecondition_goal "npfp_dequeue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "npfp_dequeue".
  Qed.
End proof_npfp_dequeue.
