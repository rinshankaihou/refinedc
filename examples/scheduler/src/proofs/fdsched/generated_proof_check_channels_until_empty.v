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
Section proof_check_channels_until_empty.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [check_channels_until_empty]. *)
  Lemma type_check_channels_until_empty (global_check_channels : loc) :
    global_check_channels ◁ᵥ global_check_channels @ function_ptr type_of_check_channels -∗
    typed_function (impl_check_channels_until_empty global_check_channels) type_of_check_channels_until_empty.
  Proof.
    Local Open Scope printing_sugar.
    start_function "check_channels_until_empty" ([[[fd_state p1] t1] errno]) => arg_fds local_err.
    prepare_parameters (fd_state p1 t1 errno).
    split_blocks ((
      <[ "#1" :=
        ∃ err : Z,
        ∃ errno : Z,
        ∃ fd_state_mid : fd_sched,
        ∃ ns_list : list (list nat),
        ∃ flag : Z,
        local_err ◁ₗ (err @ (int (i32))) ∗
        arg_fds ◁ₗ (p1 @ (&own (fd_state_mid @ (fd_t)))) ∗
        ⌜0 <= err⌝ ∗
        (curr_read_index (t1 + (num_reads_for_ns_list ns_list))) ∗
        (is_errno errno) ∗
        ⌜if (bool_decide (err = 0)) then 											fds_have_ns_list_msgs_done (input_channels fd_state) ns_list t1 else  											fds_have_ns_list_msgs (input_channels fd_state) ns_list t1⌝ ∗
        ⌜fd_state_mid = check_channels_until_empty_func t1 fd_state ns_list⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "check_channels_until_empty" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "check_channels_until_empty" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: simplify_channels; clear_cases; try solve_goal.
    2,3: destruct (bool_decide_reflect (err = 0)); first lia.
    + case_bool_decide => //=; by apply fds_have_ns_list_msgs_done_base_run.
    + case_bool_decide; by [ apply fds_have_ns_list_msgs_next_loop | apply fds_have_ns_list_msgs_done_next_run].
    + by rewrite check_channels_until_empty_next.
    all: print_sidecondition_goal "check_channels_until_empty".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "check_channels_until_empty".
  Qed.
End proof_check_channels_until_empty.
