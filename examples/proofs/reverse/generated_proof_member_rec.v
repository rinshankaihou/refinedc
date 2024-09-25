From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_member_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member_rec]. *)
  Lemma type_member_rec (global_member_rec : loc) :
    global_member_rec ◁ᵥ global_member_rec @ function_ptr type_of_member_rec -∗
    typed_function (impl_member_rec global_member_rec) type_of_member_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "member_rec" ([[l p] n]) => arg_p arg_k local_head.
    prepare_parameters (l p n).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try set_solver.
    all: print_sidecondition_goal "member_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "member_rec".
  Qed.
End proof_member_rec.
