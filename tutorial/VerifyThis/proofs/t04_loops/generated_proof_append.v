From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_code.
From refinedc.tutorial.VerifyThis.t04_loops Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t04_loops.c]. *)
Section proof_append.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append]. *)
  Lemma type_append (global_append : loc) :
    global_append ◁ᵥ global_append @ function_ptr type_of_append -∗
    typed_function (impl_append global_append) type_of_append.
  Proof.
    Local Open Scope printing_sugar.
    start_function "append" ([[p xs] ys]) => arg_l arg_k.
    prepare_parameters (p xs ys).
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
