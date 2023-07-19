From refinedc.examples.scheduler.src.fdsched Require Export message_extra.
From refinedc.examples.scheduler.src.fdsched Require Export priority_extra.
From refinedc.examples.scheduler.src.fdsched Require Export scheduler_extra.
From refinedc.typing Require Export typing.
From refinedc.examples.scheduler.src.fdsched Require Export basic_definitions.

Record fd_sched := {
    input_channels : list FD;
    sched_state : npfp_sched;
  }.

(**TODO: upstream*)
Notation array_p ly elts n :=
  (array ly (elts ++ replicate n (uninit ly)))
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

