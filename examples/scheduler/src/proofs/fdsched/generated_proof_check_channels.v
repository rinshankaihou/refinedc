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
Section proof_check_channels.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [check_channels]. *)
  Lemma type_check_channels (global_receive_messages : loc) :
    global_receive_messages ◁ᵥ global_receive_messages @ function_ptr type_of_receive_messages -∗
    typed_function (impl_check_channels global_receive_messages) type_of_check_channels.
  Proof.
    Local Open Scope printing_sugar.
    start_function "check_channels" ([[[fd_state p1] t1] errno]) => arg_fds local_ch local_fd local_flag local_err.
    prepare_parameters (fd_state p1 t1 errno).
    split_blocks ((
      <[ "#1" :=
        ∃ i : nat,
        ∃ errno : Z,
        ∃ fd_state_mid : fd_sched,
        ∃ ns : list nat,
        ∃ flag : Z,
        local_fd ◁ₗ uninit (it_layout i32) ∗
        local_err ◁ₗ uninit (it_layout i32) ∗
        local_ch ◁ₗ (i @ (int (u64))) ∗
        arg_fds ◁ₗ (p1 @ (&own (fd_state_mid @ (fd_t)))) ∗
        local_flag ◁ₗ (flag @ (int (i32))) ∗
        (curr_read_index (t1 + (num_reads_for_ns ns))) ∗
        (is_errno errno) ∗
        ⌜fds_have_n_msgs (take i (input_channels fd_state)) ns t1⌝ ∗
        ⌜ flag = bool_to_Z (bool_decide (Exists (λ n, (n <> 0)%nat) ns))⌝ ∗
        ⌜fd_state_mid = check_n_channels_func t1 fd_state i ns⌝ ∗
        ⌜(0 ≤ i ≤ length (input_channels fd_state))%nat⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "check_channels" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "check_channels" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: simplify_channels; try solve_goal.
    + rewrite Nat.add_1_r; erewrite take_S_r => //; apply fds_have_n_msgs_next_fd => //.
    + apply Exists_app; right; apply Exists_cons_hd; solve_goal.
    + rewrite receive_one_message_no_pending; by [ apply fd_has_n_msgs_implies_no_pending | rewrite -check_n_channels_S ].
    + rewrite Nat.add_1_r; erewrite take_S_r => //; apply fds_have_n_msgs_next_fd => //.
    + assert (¬ ((λ n, n <> 0) x')%nat) as HP by solve_goal; eapply Exists_last_false in HP; solve_goal.
    + rewrite receive_one_message_no_pending; by [ apply fd_has_n_msgs_implies_no_pending | rewrite -check_n_channels_S ].
    + repeat f_equal; lia.
    + erewrite <- (take_ge (input_channels _)) => //; lia.
    all: print_sidecondition_goal "check_channels".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "check_channels".
  Qed.
End proof_check_channels.
