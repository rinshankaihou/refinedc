From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo3 Require Import generated_code.
From refinedc.examples.talk_demo3 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section proof_append.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [append]. *)
  Lemma type_append (global_append : loc) :
    global_append ◁ᵥ global_append @ function_ptr type_of_append -∗
    typed_function (impl_append global_append) type_of_append.
  Proof.
    Local Open Scope printing_sugar.
    start_function "append" (p) => arg_l arg_k.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "append".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "append".
  Qed.
End proof_append.
