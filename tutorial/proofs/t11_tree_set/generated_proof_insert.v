From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_insert.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [insert]. *)
  Lemma type_insert (global_node : loc) :
    global_node ◁ᵥ global_node @ function_ptr type_of_node -∗
    typed_function (impl_insert global_node) type_of_insert.
  Proof.
    Local Open Scope printing_sugar.
    start_function "insert" ([[p s] k]) => arg_t arg_k local_cur.
    prepare_parameters (p s k).
    split_blocks ((
      <[ "#1" :=
        ∃ cur_p : loc,
        ∃ cur_s : gset Z,
        arg_k ◁ₗ (k @ (int (size_t))) ∗
        local_cur ◁ₗ (cur_p @ (&own (cur_s @ (tree_t)))) ∗
        arg_t ◁ₗ (p @ (&own (wand (cur_p ◁ₗ ({[k]} ∪ cur_s) @ tree_t) (({[k]} ∪ s) @ (tree_t)))))
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
    all: try by set_unfold; (solve_goal || naive_solver lia).
    all: print_sidecondition_goal "insert".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "insert".
  Qed.
End proof_insert.
