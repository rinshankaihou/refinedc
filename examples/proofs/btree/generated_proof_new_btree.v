From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From refinedc.examples.btree Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.btree Require Import btree_extra.
From refinedc.examples.btree Require Import btree_learn.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section proof_new_btree.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [new_btree]. *)
  Lemma type_new_btree (global_xmalloc : loc) :
    global_xmalloc ◁ᵥ global_xmalloc @ function_ptr type_of_xmalloc -∗
    typed_function (impl_new_btree global_xmalloc) type_of_new_btree.
  Proof.
    Local Open Scope printing_sugar.
    start_function "new_btree" ([]) => local_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "new_btree" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "new_btree".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "new_btree".
  Qed.
End proof_new_btree.
