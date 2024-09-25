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
Section proof_fds_add_channel.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fds_add_channel]. *)
  Lemma type_fds_add_channel (global_fcntl : loc) :
    global_fcntl ◁ᵥ global_fcntl @ function_ptr type_of_fcntl -∗
    typed_function (impl_fds_add_channel global_fcntl) type_of_fds_add_channel.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fds_add_channel" ([[fd_state p] fd]) => arg_fds arg_fd local_err.
    prepare_parameters (fd_state p fd).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fds_add_channel" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + apply list_subequiv_split; solve_goal.
    all: print_sidecondition_goal "fds_add_channel".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fds_add_channel".
  Qed.
End proof_fds_add_channel.
