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
Section proof_receive_messages.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [receive_messages]. *)
  Lemma type_receive_messages (global___builtin_errno global_receive_one_message : loc) :
    global___builtin_errno ◁ᵥ global___builtin_errno @ function_ptr type_of___builtin_errno -∗
    global_receive_one_message ◁ᵥ global_receive_one_message @ function_ptr type_of_receive_one_message -∗
    typed_function (impl_receive_messages global___builtin_errno global_receive_one_message) type_of_receive_messages.
  Proof.
    Local Open Scope printing_sugar.
    start_function "receive_messages" ([[[[fd_state p1] fd] t1] errno]) => arg_fds arg_fd local_err local_non_empty.
    prepare_parameters (fd_state p1 fd t1 errno).
    split_blocks ((
      <[ "#1" :=
        ∃ i : nat,
        ∃ err : Z,
        ∃ flag : Z,
        ∃ fd_state_mid : fd_sched,
        ∃ n : Z,
        arg_fd ◁ₗ (fd @ (int (i32))) ∗
        local_err ◁ₗ (err @ (int (i32))) ∗
        arg_fds ◁ₗ (p1 @ (&own (fd_state_mid @ (fd_t)))) ∗
        local_non_empty ◁ₗ (flag @ (int (i32))) ∗
        (curr_read_index (t1 +  (S i))) ∗
        ⌜if (bool_decide $ is_Some $ (packet_arrivals fd (t1 +  i))) then err = 0 else err = -1⌝ ∗
        ⌜ flag = if (decide (i = 0)%nat) then bool_to_Z (err =? 0) else 1⌝ ∗
        ⌜fd_state_mid = receive_n_messages_func t1 fd fd_state (S i)⌝ ∗
        (is_errno n) ∗
        ⌜if (bool_decide $ is_Some $ (packet_arrivals fd (t1 +   i))) then True else n = 80⌝ ∗
        ⌜fd_has_at_least_n_msgs fd i t1⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "receive_messages" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "receive_messages" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: rewrite <- ?Nat.add_assoc, ?Nat.add_1_r; try apply simpl_fd_has_msgs_S; solve_goal.
    all: print_sidecondition_goal "receive_messages".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "receive_messages".
  Qed.
End proof_receive_messages.
