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
Section proof_receive_one_message.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [receive_one_message]. *)
  Lemma type_receive_one_message (global_free global_npfp_enqueue global_read global_xmalloc : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_npfp_enqueue ◁ᵥ global_npfp_enqueue @ function_ptr type_of_npfp_enqueue -∗
    global_read ◁ᵥ global_read @ function_ptr type_of_read -∗
    global_xmalloc ◁ᵥ global_xmalloc @ function_ptr type_of_xmalloc -∗
    typed_function (impl_receive_one_message global_free global_npfp_enqueue global_read global_xmalloc) type_of_receive_one_message.
  Proof.
    Local Open Scope printing_sugar.
    start_function "receive_one_message" ([[[[fd_state p1] fd] t1] errno]) => arg_fds arg_fd local_msg local_n.
    prepare_parameters (fd_state p1 fd t1 errno).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "receive_one_message" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: destruct (packet_arrivals fd t1) eqn:E; try solve_goal.
    + by apply packet_data_len.
    + rewrite get_packet_data_no_pending => //=; eexists; solve_goal.
    + by rewrite get_packet_data_no_pending.
    + by rewrite receive_one_message_no_pending.
    + by rewrite /add_pending_msg_to_scheduler E.
    all: print_sidecondition_goal "receive_one_message".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "receive_one_message".
  Qed.
End proof_receive_one_message.
