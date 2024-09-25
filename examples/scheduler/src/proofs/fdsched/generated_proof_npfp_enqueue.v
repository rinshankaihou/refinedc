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
Section proof_npfp_enqueue.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [npfp_enqueue]. *)
  Lemma type_npfp_enqueue (global_message_identify_type global_message_queue_add global_priority_level_set : loc) :
    global_message_identify_type ◁ᵥ global_message_identify_type @ function_ptr type_of_message_identify_type -∗
    global_message_queue_add ◁ᵥ global_message_queue_add @ function_ptr type_of_message_queue_add -∗
    global_priority_level_set ◁ᵥ global_priority_level_set @ function_ptr type_of_priority_level_set -∗
    typed_function (impl_npfp_enqueue global_message_identify_type global_message_queue_add global_priority_level_set) type_of_npfp_enqueue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "npfp_enqueue" ([[[[m_len l1] l2] sched_state] id]) => arg_sched arg_msg local_msg_prio.
    prepare_parameters (m_len l1 l2 sched_state id).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "npfp_enqueue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + by apply msg_type_bounded.
    + apply npfp_enqueue_add_msg_to_q1. by rewrite /get_priority/update_msg_type/set_msg_type /=; simplify_option_eq.
    + rewrite /update_msg_type /set_msg_type /get_priority/add_msg_to_q/=. simplify_option_eq. symmetry. eapply list_lookup_total_insert; solve_goal.
    + eapply npfp_enqueue_create_bitmap_addmsg. by rewrite /get_priority/update_msg_type/set_msg_type/=; simplify_option_eq.
    + apply npfp_enqueue_create_bitmap_addmsg2; unfold get_priority in *; simplify_option_eq; solve_goal.
    all: print_sidecondition_goal "npfp_enqueue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "npfp_enqueue".
  Qed.
End proof_npfp_enqueue.
