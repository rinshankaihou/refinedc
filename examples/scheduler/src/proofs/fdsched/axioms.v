From refinedc.typing Require Export typing.

(** Wrapper type for file descriptors *)
Notation FD := Z (only parsing).

(** The id for a packet is given by a tuple of the FD on which it arrives and the
    value of [read_index] when it is read by the program. *)
Record packet_ID := PACKET_ID {
  fd : FD;
  read_index : nat;
}.

Section ReadIndex.
  Context `{typeG Σ}.

  Axiom curr_read_index : nat → iProp Σ.
  Axiom is_errno : Z → iProp Σ.

End ReadIndex.


Notation num_msg_types := (max_int u8 + 1) (only parsing).

(** function to look up the type of the message *)
Axiom message_identify_type_coq : packet_ID → nat.

Axiom msg_type_bounded : ∀ msg, message_identify_type_coq msg < num_msg_types.
