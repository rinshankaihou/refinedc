From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_member.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member]. *)
  Lemma type_member :
    ⊢ typed_function impl_member type_of_member.
  Proof.
    Local Open Scope printing_sugar.
    start_function "member" ([[p t] k]) => arg_t arg_k local_cur.
    prepare_parameters (p t k).
    split_blocks ((
      <[ "#1" :=
        ∃ p_cur : loc,
        ∃ branch : tree Z,
        arg_k ◁ₗ (k @ (int (i32))) ∗
        local_cur ◁ₗ (p_cur @ (&own (branch @ (tree_t)))) ∗
        arg_t ◁ₗ (p @ (&own (wand (p_cur ◁ₗ branch @ tree_t) (t @ (tree_t))))) ∗
        ⌜tree_member k t ↔ tree_member k branch⌝
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
    all: print_sidecondition_goal "member".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "member".
  Qed.
End proof_member.
