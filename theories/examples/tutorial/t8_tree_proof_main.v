From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t8_tree_code.
From refinedc.examples.tutorial Require Import t8_tree_spec.
From refinedc.examples.tutorial Require Import t8_tree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t8_tree.c]. *)
Section proof_main.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [main]. *)
  Lemma type_main (sempty sinit sfree_tree smember sinsert sremove : loc) :
    sempty ◁ᵥ sempty @ function_ptr type_of_sempty -∗
    sinit ◁ᵥ sinit @ function_ptr type_of_sinit -∗
    sfree_tree ◁ᵥ sfree_tree @ function_ptr type_of_sfree_tree -∗
    smember ◁ᵥ smember @ function_ptr type_of_smember -∗
    sinsert ◁ᵥ sinsert @ function_ptr type_of_sinsert -∗
    sremove ◁ᵥ sremove @ function_ptr type_of_sremove -∗
    typed_function (impl_main sempty sinit sfree_tree smember sinsert sremove) type_of_main.
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
