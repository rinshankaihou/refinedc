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
Section proof_message_queue_remove.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [message_queue_remove]. *)
  Lemma type_message_queue_remove (global_message_queue_empty : loc) :
    global_message_queue_empty ◁ᵥ global_message_queue_empty @ function_ptr type_of_message_queue_empty -∗
    typed_function (impl_message_queue_remove global_message_queue_empty) type_of_message_queue_remove.
  Proof.
    Local Open Scope printing_sugar.
    start_function "message_queue_remove" ([data q]) => arg_q local_head.
    prepare_parameters (data q).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "message_queue_remove" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "message_queue_remove".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "message_queue_remove".
  Qed.
End proof_message_queue_remove.
