From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_insert.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [insert]. *)
  Lemma type_insert (global_node : loc) :
    global_node ◁ᵥ global_node @ function_ptr type_of_node -∗
    typed_function (impl_insert global_node) type_of_insert.
  Proof.
    Local Open Scope printing_sugar.
    start_function "insert" ([[p t] k]) => arg_t arg_k local_cur.
    prepare_parameters (p t k).
    split_blocks ((
      <[ "#1" :=
        ∃ p_cur : loc,
        ∃ branch : tree Z,
        arg_k ◁ₗ (k @ (int (i32))) ∗
        local_cur ◁ₗ (p_cur @ (&own (branch @ (tree_t)))) ∗
        arg_t ◁ₗ (p @ (&own (wand (p_cur ◁ₗ (tree_insert k branch) @ tree_t) ((tree_insert k t) @ (tree_t)))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "insert" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "insert" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "insert".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "insert".
  Qed.
End proof_insert.
