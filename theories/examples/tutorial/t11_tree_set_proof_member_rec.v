From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t11_tree_set_code.
From refinedc.examples.tutorial Require Import t11_tree_set_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t11_tree_set.c]. *)
Section proof_member_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member_rec]. *)
  Lemma type_member_rec (member_rec : loc) :
    member_rec ◁ᵥ member_rec @ function_ptr type_of_member_rec -∗
    typed_function (impl_member_rec member_rec) type_of_member_rec.
  Proof.
    start_function "member_rec" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member_rec" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by set_unfold; naive_solver lia.
    all: print_sidecondition_goal "member_rec".
  Qed.
End proof_member_rec.
