From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t8_tree_code.
From refinedc.examples.tutorial Require Import t8_tree_spec.
From refinedc.examples.tutorial Require Import t8_tree_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t8_tree.c]. *)
Section proof_smember.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [smember]. *)
  Lemma type_smember (member : loc) :
    member ◁ᵥ member @ function_ptr type_of_member -∗
    typed_function (impl_smember member) type_of_smember.
  Proof.
    start_function "smember" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "smember" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by etrans; [done|]; symmetry; apply tree_rel_member.
    all: print_sidecondition_goal "smember".
  Qed.
End proof_smember.
