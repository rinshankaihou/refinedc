From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_dequeue.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [dequeue]. *)
  Lemma type_dequeue (global_free : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    typed_function (impl_dequeue global_free) type_of_dequeue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "dequeue" ([p tys]) => arg_q local_elem local_ret.
    prepare_parameters (p tys).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "dequeue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "dequeue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "dequeue".
  Qed.
End proof_dequeue.
