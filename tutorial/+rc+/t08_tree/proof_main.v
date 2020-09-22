From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import code.
From refinedc.tutorial.t08_tree Require Import spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (sempty sfree_tree sinit sinsert smember sremove : loc) :
    sempty ◁ᵥ sempty @ function_ptr type_of_sempty -∗
    sfree_tree ◁ᵥ sfree_tree @ function_ptr type_of_sfree_tree -∗
    sinit ◁ᵥ sinit @ function_ptr type_of_sinit -∗
    sinsert ◁ᵥ sinsert @ function_ptr type_of_sinsert -∗
    smember ◁ᵥ smember @ function_ptr type_of_smember -∗
    sremove ◁ᵥ sremove @ function_ptr type_of_sremove -∗
    typed_function (impl_main sempty sfree_tree sinit sinsert smember sremove) type_of_main.
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
