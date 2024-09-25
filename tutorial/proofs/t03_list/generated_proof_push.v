From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_push.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [push]. *)
  Lemma type_push (global_talloc : loc) :
    global_talloc ◁ᵥ global_talloc @ function_ptr type_of_talloc -∗
    typed_function (impl_push global_talloc) type_of_push.
  Proof.
    Local Open Scope printing_sugar.
    start_function "push" ([l ty]) => arg_p arg_e local_node.
    prepare_parameters (l ty).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "push" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "push".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "push".
  Qed.
End proof_push.
