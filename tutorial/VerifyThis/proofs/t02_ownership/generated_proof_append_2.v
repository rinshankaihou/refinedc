From refinedc.typing Require Import typing.
From refinedc.tutorial.VerifyThis.t02_ownership Require Import generated_code.
From refinedc.tutorial.VerifyThis.t02_ownership Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/VerifyThis/t02_ownership.c]. *)
Section proof_append_2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append_2]. *)
  Lemma type_append_2 (global_append_2 : loc) :
    global_append_2 ◁ᵥ global_append_2 @ function_ptr type_of_append_2 -∗
    typed_function (impl_append_2 global_append_2) type_of_append_2.
  Proof.
    Local Open Scope printing_sugar.
    start_function "append_2" (p) => arg_l arg_k.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append_2" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "append_2".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "append_2".
  Qed.
End proof_append_2.
