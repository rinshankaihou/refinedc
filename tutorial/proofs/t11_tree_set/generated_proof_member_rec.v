From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_member_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member_rec]. *)
  Lemma type_member_rec (global_member_rec : loc) :
    global_member_rec ◁ᵥ global_member_rec @ function_ptr type_of_member_rec -∗
    typed_function (impl_member_rec global_member_rec) type_of_member_rec.
  Proof.
    start_function "member_rec" ([[p s] k]) => arg_t arg_k.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member_rec" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_unfold; naive_solver lia.
    all: print_sidecondition_goal "member_rec".
  Qed.
End proof_member_rec.
