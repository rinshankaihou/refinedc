From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_init_queue.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [init_queue]. *)
  Lemma type_init_queue (global_xmalloc : loc) :
    global_xmalloc ◁ᵥ global_xmalloc @ function_ptr type_of_xmalloc -∗
    typed_function (impl_init_queue global_xmalloc) type_of_init_queue.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init_queue" ([]) => local_queue.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_queue" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_queue".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init_queue".
  Qed.
End proof_init_queue.
