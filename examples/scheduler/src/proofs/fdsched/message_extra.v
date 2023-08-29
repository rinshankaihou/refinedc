From refinedc.typing Require Import typing.
From refinedc.examples.scheduler.src.fdsched Require Export basic_definitions.

#[projections(primitive)]
Record message_data := Message {
  m_type : nat;
  m_length : Z;
  m_id : packet_ID
}.

Global Instance message_data_inhabited : Inhabited message_data :=
  populate (Message inhabitant inhabitant inhabitant).

(** function to set type of a message to a given value*)
Definition set_msg_type (msg : message_data) (type : nat) := {|
  m_type := type;
  m_length := m_length msg;
  m_id := m_id msg
|}.

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
