From refinedc.typing Require Export typing.

(** Wrapper type for file descriptors *)
Notation FD := Z (only parsing).

(** the ID for a packet is given by a tuple of fd, time and index in the arrivals at that time *)
Record packet_ID := PACKET_ID {
  fd : FD;
  arr_time : nat;
  index : nat;
}.

(** The data type for interesting events we record in the log*)
Inductive LogEntry :=
| read_from_socket (j : packet_ID) (t : nat)
| callback_dispatched (j : packet_ID) (t : nat)
| callback_returned (j : packet_ID) (t : nat).

Section EventLog.
  Context `{typeG Σ}.

  Axiom curr_time : nat → iProp Σ.
  Axiom curr_log : list LogEntry → iProp Σ.

End EventLog.

(** function to look up the type of the message *)
Notation num_msg_types := (max_int u8 + 1) (only parsing).

Axiom message_identify_type_coq : packet_ID → nat.

Axiom msg_type_bounded : ∀ msg, message_identify_type_coq msg < num_msg_types.
