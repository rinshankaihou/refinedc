From refinedc.typing Require Import typing.
From refinedc.examples.scheduler.src.fdsched Require Export basic_definitions.

Definition max_msg_len : Z :=
  4096 - ly_size u8 - ly_size size_t - ly_size void*.

#[projections(primitive)]
Record message_data := Message {
  m_type : nat;
  m_length : Z;
  m_id : packet_ID
}.

Global Instance packet_ID_inhabited : Inhabited packet_ID :=
  populate (PACKET_ID inhabitant inhabitant inhabitant).

Global Instance message_data_inhabited : Inhabited message_data :=
  populate (Message inhabitant inhabitant inhabitant).

Notation num_msg_types := (max_int u8 + 1) (only parsing).

(** function to set type of a message to a given value*)
Definition set_msg_type (msg : message_data) (type : nat) := {|
  m_type := type;
  m_length := m_length msg;
  m_id := m_id msg
|}.

(** function to look up the type of the message *)
Axiom message_identify_type_coq : packet_ID → nat.

Axiom msg_type_bounded: ∀ msg : message_data, message_identify_type_coq (m_id msg) < num_msg_types.

(** sets the type field of the message to the correct type *)
Definition update_msg_type (msg : message_data) : message_data :=
  let type := message_identify_type_coq (m_id msg) in
  set_msg_type msg type.

Global Instance SimplExistMessageData Σ : @SimplExist Σ message_data
  (λ P, ∃ type len id, P {|
    m_type := type;
    m_length := len;
    m_id := id
|})%I.
Proof. iIntros (?) "(%&%&%&?)". by iExists _. Qed.
