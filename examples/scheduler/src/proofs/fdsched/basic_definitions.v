From refinedc.typing Require Export typing.

(** Wrapper type for file descriptors *)
Notation FD := Z (only parsing).

(** the ID for a packet is given by a tuple of fd, time and index in the arrivals at that time *)
Record packet_ID := PACKET_ID {
   fd : FD;
   arr_time : nat;
   index : nat
}.

(** We parameterize the whole proof by a ground truth of arrivals *)
Notation pdata := (list Z) (only parsing).
Class PacketArrivals := {
  packet_arrivals : nat → FD → list pdata
}.

Section READ.
  Context `{!PacketArrivals}.

  (** function to compute data of a packet given its ID *)
  Definition get_packet_data (ID : packet_ID) : pdata :=
    packet_arrivals (arr_time ID) (fd ID) !!! index ID.

End READ.
