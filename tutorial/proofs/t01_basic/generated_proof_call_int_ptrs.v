From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_call_int_ptrs.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [call_int_ptrs]. *)
  Lemma type_call_int_ptrs (global_int_ptrs : loc) :
    global_int_ptrs ◁ᵥ global_int_ptrs @ function_ptr type_of_int_ptrs -∗
    typed_function (impl_call_int_ptrs global_int_ptrs) type_of_call_int_ptrs.
  Proof.
    Local Open Scope printing_sugar.
    start_function "call_int_ptrs" ([]) => local_p1 local_p2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "call_int_ptrs" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "call_int_ptrs".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "call_int_ptrs".
  Qed.
End proof_call_int_ptrs.
