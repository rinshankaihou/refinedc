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
Section proof_priority_level_set.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [priority_level_set]. *)
  Lemma type_priority_level_set :
    ⊢ typed_function impl_priority_level_set type_of_priority_level_set.
  Proof.
    Local Open Scope printing_sugar.
    start_function "priority_level_set" ([[p priority] bm]) => arg_bm arg_prio local_bit local_word.
    prepare_parameters (p priority bm).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "priority_level_set" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + by apply Z_shiftl_1_range; solve_goal.
    + to_div_mod. by apply priority_level_set_clear_rest.
    + to_div_mod. by eapply priority_level_set_changed.
    all: print_sidecondition_goal "priority_level_set".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "priority_level_set".
  Qed.
End proof_priority_level_set.
