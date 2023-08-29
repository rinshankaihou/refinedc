From refinedc.typing Require Export typing.
From refinedc.examples.scheduler.src.fdsched Require Export axioms.

Definition max_msg_len : Z :=
  (4096 - ly_size u8 - ly_size size_t - ly_size void* ).
Global Opaque max_msg_len.

Global Instance packet_ID_inhabited : Inhabited packet_ID :=
  populate {|fd := inhabitant; arr_time := inhabitant; index := inhabitant|}.

(** We parameterize the whole proof by a ground truth of arrivals *)
Notation pdata := (list Z) (only parsing).
Class PacketArrivals := {
  packet_arrivals : nat → FD → list pdata
}.

Global Instance DecisionID : EqDecision packet_ID.
Proof.
  solve_decision.
Qed.

Section EventLog.
  Context `{typeG Σ}.

  Global Instance curr_log_related_to A l : RelatedTo (Σ := Σ) (λ x : A,curr_log (l x)) :=
    {|rt_fic := FindDirect (λ l1, curr_log l1)%I |}.
  Global Instance curr_time_related_to A t : RelatedTo (Σ := Σ) (λ x : A,curr_time (t x)) :=
    {|rt_fic := FindDirect (λ t, curr_time t)%I |}.
  Lemma subsume_curr_log B l l1 G :
    (∃ x, ⌜l = l1 x⌝ ∗ G x)
    ⊢ subsume (Σ := Σ) (curr_log l) (λ x : B, curr_log (l1 x)) G.
  Proof. iIntros "(%x & -> & ?) Hcurr". iExists _. iFrame. Qed.
  Definition subsume_curr_log_inst := [instance subsume_curr_log].
  Global Existing Instance subsume_curr_log_inst.

  Lemma subsume_curr_time B t t1 G:
    (∃ x, ⌜t = t1 x⌝ ∗ G x)
    ⊢ subsume (Σ := Σ) (curr_time t) (λ x : B, curr_time (t1 x)) G.
  Proof. iIntros "(%x & -> & ?) Hcurr". iExists _. iFrame. Qed.
  Definition subsume_curr_time_inst := [instance subsume_curr_time].
  Global Existing Instance subsume_curr_time_inst.

End EventLog.

(** function to compute IDs of packets read so far *)
Definition read_so_far_ID (l : list LogEntry) : list packet_ID :=
  omap (λ e, if e is read_from_socket j _ then Some j else None) l.

Section ReadSpecs.
  Context `{!PacketArrivals}.

  (** Lookup in the arrival sequence using the ID. *)
  Definition get_packet_data (ID : packet_ID) : pdata :=
    packet_arrivals (arr_time ID) (fd ID) !!! index ID.

  (** function to compute data of a packet given its ID *)
  Definition get_packet_data_option (ID : option packet_ID) : list Z:=
    from_option get_packet_data inhabitant ID.

  (** Get list of n packet IDs arriving at time t *)
  Definition get_list_packets t (n : nat) (curr_fd : FD) : list packet_ID :=
    (λ n, {|arr_time := t; index := n; fd := curr_fd|}) <$> seq 0 n.

  (** list of packet ID's that have arrived at time [t] *)
  Definition IDs_arrived_at  (t : nat) (fd : FD) : list packet_ID :=
    let arrivals_at_t := packet_arrivals t fd in
    let len := length arrivals_at_t in
    get_list_packets t len fd.

  (** Given a current time and a file descriptor generate all the packet IDs
      that have arrived so far. *)
  Definition IDs_arrived_upto (t : nat) (fd : FD) : list packet_ID :=
    seq 0 t ≫= (λ n, IDs_arrived_at n fd ).

  (** all the packet IDs that have arrived but not been read yet *)
  Definition get_pending_packets_from_given_fd (t : nat) (l: list LogEntry) (fd : FD)
    : list packet_ID :=
    list_difference (IDs_arrived_upto t fd) (read_so_far_ID l).

  (** get the ID of the head of pending packets list *)
  Definition get_head_ID_option (t : nat) (l : list LogEntry) (fd : FD) : option packet_ID :=
    head (get_pending_packets_from_given_fd t l fd).

  (** get the ID of the head of pending packets list *)
  Definition get_head_ID (t : nat) (l : list LogEntry) (fd : FD) : packet_ID :=
    default inhabitant (get_head_ID_option t l fd).

End ReadSpecs.

Global Opaque get_packet_data_option.
