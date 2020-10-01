From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_member.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [member]. *)
  Lemma type_member :
    ⊢ typed_function impl_member type_of_member.
  Proof.
    start_function "member" ([[l p] n]) => arg_p arg_k local_prev local_cur local_head.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : list Z,
        ∃ pc : loc,
        arg_k ◁ₗ (n @ (int (size_t))) ∗
        local_cur ◁ₗ uninit LPtr ∗
        local_head ◁ₗ uninit LPtr ∗
        local_prev ◁ₗ (pc @ (&own ((l1 `at_type` int size_t) @ (list_t)))) ∗
        arg_p ◁ₗ (p @ (&own (wand (pc ◁ₗ (l1 `at_type` int size_t) @ list_t) ((l `at_type` int size_t) @ (list_t))))) ∗
        ⌜n ∈ l ↔ n ∈ l1⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "member" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try set_unfold; refined_solver.
    all: print_sidecondition_goal "member".
  Qed.
End proof_member.
