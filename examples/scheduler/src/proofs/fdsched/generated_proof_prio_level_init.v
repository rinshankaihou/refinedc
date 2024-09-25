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
Section proof_prio_level_init.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!PacketArrivals}.
  Context `{!mallocG Σ}.

  (* Typing proof for [prio_level_init]. *)
  Lemma type_prio_level_init :
    ⊢ typed_function impl_prio_level_init type_of_prio_level_init.
  Proof.
    Local Open Scope printing_sugar.
    start_function "prio_level_init" (p) => arg_bm local_lvl.
    prepare_parameters (p).
    split_blocks ((
      <[ "#1" :=
        ∃ i : nat,
        local_lvl ◁ₗ (i @ (int (i32))) ∗
        arg_bm ◁ₗ (p @ (&own (struct (struct_prio_bitmap) [@{type} array_p (u64) (replicate i 0 `at_type` int u64) (4%nat) ]))) ∗
        ⌜0 <= i <= 4⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "prio_level_init" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "prio_level_init" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + by apply list_subequiv_split; solve_goal.
    + by have -> : i = 4%nat by [lia]; compute_done.
    + by have -> : i = 4%nat by [lia]; compute_done.
    all: print_sidecondition_goal "prio_level_init".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "prio_level_init".
  Qed.
End proof_prio_level_init.
