From refinedc.typing Require Import typing.
From refinedc.examples.queue Require Import generated_code.
From refinedc.examples.queue Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/queue.c]. *)
Section proof_is_empty.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [is_empty]. *)
  Lemma type_is_empty :
    ⊢ typed_function impl_is_empty type_of_is_empty.
  Proof.
    Local Open Scope printing_sugar.
    start_function "is_empty" ([p tys]) => arg_q.
    prepare_parameters (p tys).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "is_empty" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "is_empty".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "is_empty".
  Qed.
End proof_is_empty.
