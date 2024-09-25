From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_member.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member]. *)
  Lemma type_member :
    ⊢ typed_function impl_member type_of_member.
  Proof.
    Local Open Scope printing_sugar.
    start_function "member" ([[p s] k]) => arg_t arg_k local_cur.
    prepare_parameters (p s k).
    split_blocks ((
      <[ "#1" :=
        ∃ cur_p : loc,
        ∃ cur_s : gset Z,
        arg_k ◁ₗ (k @ (int (size_t))) ∗
        local_cur ◁ₗ (cur_p @ (&own (cur_s @ (tree_t)))) ∗
        arg_t ◁ₗ (p @ (&own (wand (cur_p ◁ₗ cur_s @ tree_t) (s @ (tree_t))))) ∗
        ⌜k ∈ s ↔ k ∈ cur_s⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_unfold; naive_solver lia.
    all: print_sidecondition_goal "member".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "member".
  Qed.
End proof_member.
