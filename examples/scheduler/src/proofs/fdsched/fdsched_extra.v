From refinedc.examples.scheduler.src.fdsched Require Export message_extra.
From refinedc.examples.scheduler.src.fdsched Require Export priority_extra.
From refinedc.examples.scheduler.src.fdsched Require Export scheduler_extra.
From refinedc.typing Require Export typing.
From refinedc.examples.scheduler.src.fdsched Require Export basic_definitions.

Record fd_sched := {
    input_channels : list FD;
    sched_state : npfp_sched;
  }.

(* TODO: upstream *)
Notation array_p ly elts n :=
  (array ly (elts ++ replicate (n - length elts) (uninit ly)))
  (only parsing).

Program Definition fds_set_callback_func (fds : fd_sched)  (type prio : nat) :=
  {|
    input_channels := input_channels fds;
    sched_state := {|
                    callbacks := <[type := prio]> (callbacks (sched_state fds));
                    msg_qs := msg_qs (sched_state fds);
                  |}
  |}.
Next Obligation.
  move => [? [? ? ? ?]] type prio.
  by rewrite insert_length.
Qed.
Next Obligation.
  by move => [? [? ? ? ?]] _ _ .
Qed.

Definition fds_add_channel_func (fd_state : fd_sched) (fd : FD) :=
  {|
    input_channels := fd_state.(input_channels) ++ [fd];
    sched_state := fd_state.(sched_state)
  |}.

Section RecieveOneMessageSpecification.

  Context `{!PacketArrivals}.

   (** Given a packet ID, generate the message corresponding to that packet ID *)
  Definition generate_msg_corresponding_to_packetID (id : packet_ID) : message_data :=
    {|m_type := inhabitant; m_length := max_msg_len; m_id := id|}.

  (** if pending packets is empty then add nothing to the scheduler else add
      the right message to the scheduler. *)
  Definition add_pending_msg_to_scheduler (t :nat) (l1 : list LogEntry) (fd : FD) (sched_state : npfp_sched) : npfp_sched :=
    let ID := (get_head_ID t l1 fd) in
    let pending := get_pending_packets_from_given_fd t l1 fd in
    if decide (pending = []) then sched_state else
      let msg := generate_msg_corresponding_to_packetID ID in
      npfp_enqueue_func sched_state msg.

  Definition receive_one_message_func (t :nat) (l : list LogEntry) (fd :FD) (fd_state : fd_sched) : fd_sched :=
    {|
      input_channels := fd_state.(input_channels);
      sched_state := add_pending_msg_to_scheduler t l fd fd_state.(sched_state);
    |}.

End RecieveOneMessageSpecification.

Section RecieveOneMessageProof.
  Context `{!PacketArrivals} `{!typeG Σ}.

  Global Instance simpl_and_npfp_enqueue_func fd_state msg1 msg2:
    SimplAndUnsafe (npfp_enqueue_func (sched_state fd_state) msg1 =
                    npfp_enqueue_func (sched_state fd_state) msg2) (msg1 = msg2) .
  Proof. by move => ->. Qed.

  Global Instance simpl_and_get_packet_data_option_inst (n : packet_ID) t1 l fd
    `{CanSolve (is_Some (get_head_ID_option t1 l fd))}
    `{!IsEx n}:
    SimplAndUnsafe
      (get_packet_data_option (get_head_ID_option t1 l fd) `at_type` (int u8) ++
         replicate (Z.to_nat max_msg_len -
                      length (get_packet_data_option (get_head_ID_option t1 l fd)))
         (uninit u8) =
         get_packet_data  n `at_type` (int u8) ++
           replicate (Z.to_nat max_msg_len - length (get_packet_data_option (Some n)))
           (uninit u8))%I
      (n = hd inhabitant (get_pending_packets_from_given_fd t1 l fd)).
  Proof.
    rename select (CanSolve _) into HSome.
    rewrite /CanSolve /get_head_ID_option in HSome.
    move => ->.
    case (get_pending_packets_from_given_fd t1 l fd) eqn: EQ; first by contradict HSome.
    by rewrite /get_head_ID_option EQ //=.
  Qed.

  Global Instance simpl_and_message_equality msg1 msg2 :
    SimplAnd (msg1 = msg2)
      (msg1.(m_type) = msg2.(m_type)
       ∧ msg1.(m_length) = msg2.(m_length)
       ∧ msg1.(m_id) = msg2.(m_id)).
  Proof. destruct msg1, msg2. split; naive_solver. Qed.

  Lemma recvonemsg0 t1 l fd:
    (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
    ∃ n' : nat,
      (get_packet_data_option (get_head_ID_option t1 l fd) `at_type` (int u8))%I =
        replicate n' (uninit u8)
      ∧ replicate (Z.to_nat max_msg_len - length (get_packet_data_option (get_head_ID_option t1 l fd)))
          (uninit u8) =
          replicate
            (length (get_packet_data_option (get_head_ID_option t1 l fd)) +
               (Z.to_nat max_msg_len - length (get_packet_data_option (get_head_ID_option t1 l fd))) - n')
            (uninit u8)
      ∧ (n' <=
           length (get_packet_data_option (get_head_ID_option t1 l fd)) +
             (Z.to_nat max_msg_len - length (get_packet_data_option (get_head_ID_option t1 l fd))))%nat.
  Proof.
    exists 0%nat; split.
    * unfold_opaque @get_packet_data_option.
      have Hfalse: (¬ is_Some (get_head_ID_option t1 l fd)) by solve_goal.
      rewrite -eq_None_not_Some in Hfalse.
      by rewrite Hfalse.
    * split; try solve_goal.
      have Hfalse: (¬ is_Some (get_head_ID_option t1 l fd)) by solve_goal.
      rewrite -eq_None_not_Some in Hfalse.
      rewrite Hfalse. unfold_opaque @get_packet_data_option.
      simpl.
      solve_goal.
  Qed.

  Lemma recvonemsg1 t1 l fd:
     (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
     (ly_size u8 * 4079)%nat =
  (ly_size u8 *
   (length (get_packet_data_option (get_head_ID_option t1 l fd)) +
      (Z.to_nat max_msg_len - length (get_packet_data_option (get_head_ID_option t1 l fd)))))%nat.
  Proof.
    move => ?.
    have Hfalse: (¬ is_Some (get_head_ID_option t1 l fd)) by solve_goal.
    rewrite -eq_None_not_Some in Hfalse.
    rewrite !Hfalse. unfold_opaque @get_packet_data_option.
    simpl.
    solve_goal.
    Qed.

  Lemma recvonemsg2 t1 l fd :
    (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
    (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) =
      (if decide (get_pending_packets_from_given_fd t1 l fd = []) then -1 else 0).
  Proof.
    move => ?.
    rewrite /get_head_ID_option.
    case (get_pending_packets_from_given_fd t1 l fd) eqn:EQ; first by done.
    have Hfalse: bool_decide (is_Some (get_head_ID_option t1 l fd)) = false by solve_goal.
    by rewrite /get_head_ID bool_decide_eq_false -eq_None_not_Some head_None EQ in Hfalse.
  Qed.

  Lemma recvonemsg3 t1 l fd fd_state :
    (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
    fd_state = receive_one_message_func t1 l fd fd_state.
  Proof.
    move => ?.
    have Hfalse: bool_decide (is_Some (get_head_ID_option t1 l fd)) = false by solve_goal.
    rewrite /get_head_ID bool_decide_eq_false -eq_None_not_Some head_None in Hfalse.
    rewrite /receive_one_message_func /add_pending_msg_to_scheduler !Hfalse //=.
    destruct fd_state; f_equiv; done.
  Qed.

  Lemma recvonemsg4 t1 l fd :
    ¬ (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
    0 = (if decide (get_pending_packets_from_given_fd t1 l fd = []) then -1 else 0).
  Proof.
    move => ?.
    have Htrue: bool_decide (is_Some (get_head_ID_option t1 l fd)) = true by solve_goal.
    rewrite /get_head_ID_option bool_decide_eq_true in Htrue.
    rewrite decide_bool_decide.
    case (bool_decide (get_pending_packets_from_given_fd t1 l fd = [])) eqn: EQ; try done.
    rewrite bool_decide_eq_true in EQ.
    rewrite EQ in Htrue.
    by contradict Htrue.
  Qed.

  Lemma recvonemsg5 t1 l fd fd_state:
    ¬ (if bool_decide (is_Some (get_head_ID_option t1 l fd)) then max_msg_len else -1) ≤ 0 →
    npfp_enqueue_func (sched_state fd_state)
                      {|
                        m_type :=
                          message_identify_type_coq
                            (hd inhabitant (get_pending_packets_from_given_fd t1 l fd));
                        m_length := if bool_decide (is_Some (get_head_ID_option t1 l fd))
                                    then max_msg_len else -1;
                        m_id := hd inhabitant (get_pending_packets_from_given_fd t1 l fd)
                      |}
    = add_pending_msg_to_scheduler t1 l fd (sched_state fd_state).
  Proof.
    move => ?.
    have Htrue: bool_decide (is_Some (get_head_ID_option t1 l fd)) = true by solve_goal.
    rewrite  /add_pending_msg_to_scheduler !Htrue //= decide_bool_decide.
    rewrite bool_decide_eq_true /get_head_ID_option in Htrue.
    have ->: bool_decide (get_pending_packets_from_given_fd t1 l fd = []) = false
        by rewrite bool_decide_eq_false -head_is_Some.
    rewrite /get_priority /npfp_enqueue_func.
    case (get_pending_packets_from_given_fd t1 l fd) eqn:EQ; first by contradict Htrue.
    f_equiv; rewrite /hd; last by rewrite /get_head_ID /get_head_ID_option EQ //=.
    by rewrite /generate_msg_corresponding_to_packetID /get_head_ID /get_head_ID_option EQ //= max_msg_len_simpl.
  Qed.

End RecieveOneMessageProof.
