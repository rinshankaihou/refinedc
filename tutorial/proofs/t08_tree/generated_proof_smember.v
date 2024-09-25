From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_smember.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [smember]. *)
  Lemma type_smember (global_member : loc) :
    global_member ◁ᵥ global_member @ function_ptr type_of_member -∗
    typed_function (impl_smember global_member) type_of_smember.
  Proof.
    Local Open Scope printing_sugar.
    start_function "smember" ([[p s] k]) => arg_t arg_k.
    prepare_parameters (p s k).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "smember" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by etrans; [done|]; symmetry; apply tree_rel_member.
    all: print_sidecondition_goal "smember".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "smember".
  Qed.
End proof_smember.
