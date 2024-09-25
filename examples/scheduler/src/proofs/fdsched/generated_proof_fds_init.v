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
Section proof_fds_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [fds_init]. *)
  Lemma type_fds_init (global_nop_callback global_prio_level_init : loc) :
    global_nop_callback ◁ᵥ global_nop_callback @ function_ptr type_of_nop_callback -∗
    global_prio_level_init ◁ᵥ global_prio_level_init @ function_ptr type_of_prio_level_init -∗
    typed_function (impl_fds_init global_nop_callback global_prio_level_init) type_of_fds_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "fds_init" ([fds_refn p]) => arg_fds local_prio local_typ.
    prepare_parameters (fds_refn p).
    split_blocks ((
      <[ "#4" :=
        ∃ priority : nat,
        local_typ ◁ₗ uninit (it_layout i32) ∗
        local_prio ◁ₗ (priority @ (int (i32))) ∗
        arg_fds ◁ₗ (p @ (&own (struct (struct_fd_scheduler) [@{type} uninit (mk_array_layout i32 16) ; (0) @ (int (u64)) ; struct (struct_npfp_scheduler) [@{type} array (layout_of struct_callback) (replicate (Z.to_nat num_msg_types) 0%nat `at_type` callback_t) ; array_p (struct_message_queue) (replicate priority (@nil message_data) `at_type`  message_queue) (Z.to_nat num_priorities) ; (replicate (Z.to_nat num_priorities) false) @ (prio_bitmap_t) ] ]))) ∗
        ⌜priority ≤ num_priorities⌝
    ]> $
      <[ "#1" :=
        ∃ i : nat,
        local_prio ◁ₗ uninit (it_layout i32) ∗
        local_typ ◁ₗ (i @ (int (i32))) ∗
        arg_fds ◁ₗ (p @ (&own (struct (struct_fd_scheduler) [@{type} uninit (mk_array_layout i32 16) ; (0) @ (int (u64)) ; struct (struct_npfp_scheduler) [@{type} array_p (layout_of struct_callback) (replicate i 0%nat `at_type` callback_t) (Z.to_nat num_msg_types) ; uninit (mk_array_layout struct_message_queue (Z.to_nat num_priorities)) ; (replicate (Z.to_nat num_priorities) false) @ (prio_bitmap_t) ] ]))) ∗
        ⌜i ≤ num_msg_types⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fds_init" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fds_init" "#4".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "fds_init" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + by apply list_subequiv_split; solve_goal.
    + have Hprio: priority = (Z.to_nat num_priorities); solve_goal.
    + by apply list_subequiv_split; solve_goal.
    + have Hi: i = (Z.to_nat num_msg_types); solve_goal.
    all: print_sidecondition_goal "fds_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "fds_init".
  Qed.
End proof_fds_init.
