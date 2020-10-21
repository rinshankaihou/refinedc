From refinedc.typing Require Import typing.
From refinedc.tutorial.t08_tree Require Import generated_code.
From refinedc.tutorial.t08_tree Require Import generated_spec.
From refinedc.tutorial.t08_tree Require Import t08_tree_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t08_tree.c]. *)
Section proof_member_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member_rec]. *)
  Lemma type_member_rec (member_rec : loc) :
    member_rec ◁ᵥ member_rec @ function_ptr type_of_member_rec -∗
    typed_function (impl_member_rec member_rec) type_of_member_rec.
  Proof.
    start_function "member_rec" ([[p t] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member_rec" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "member_rec".
  Qed.
End proof_member_rec.
