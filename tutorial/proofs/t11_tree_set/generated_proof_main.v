From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (empty free_tree init insert member remove : loc) :
    empty ◁ᵥ empty @ function_ptr type_of_empty -∗
    free_tree ◁ᵥ free_tree @ function_ptr type_of_free_tree -∗
    init ◁ᵥ init @ function_ptr type_of_init -∗
    insert ◁ᵥ insert @ function_ptr type_of_insert -∗
    member ◁ᵥ member @ function_ptr type_of_member -∗
    remove ◁ᵥ remove @ function_ptr type_of_remove -∗
    typed_function (impl_main empty free_tree init insert member remove) type_of_main.
  Proof.
    start_function "main" ([]) => local_t.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "main" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "main".
  Qed.
End proof_main.
