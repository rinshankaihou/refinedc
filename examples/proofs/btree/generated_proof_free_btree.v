From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From refinedc.examples.btree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.btree Require Import btree_extra.
From refinedc.examples.btree Require Import btree_learn.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section proof_free_btree.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [free_btree]. *)
  Lemma type_free_btree (global_free global_free_btree_nodes : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_free_btree_nodes ◁ᵥ global_free_btree_nodes @ function_ptr type_of_free_btree_nodes -∗
    typed_function (impl_free_btree global_free global_free_btree_nodes) type_of_free_btree.
  Proof.
    Local Open Scope printing_sugar.
    start_function "free_btree" ([]) => arg_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free_btree" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "free_btree".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "free_btree".
  Qed.
End proof_free_btree.
