From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t3_list_code.
From refinedc.examples.tutorial Require Import t3_list_spec.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t3_list.c]. *)
Section proof_rev_append.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [rev_append]. *)
  Lemma type_rev_append :
    ⊢ typed_function impl_rev_append type_of_rev_append.
  Proof.
    start_function "rev_append" ([[p l1] l2]) => arg_l1 arg_l2 local_cur local_cur_tail.
    split_blocks ((
      <[ "#1" :=
        ∃ l1_prefix : list type,
        ∃ l1_suffix : list type,
        ∃ cur_l2 : list type,
        local_cur_tail ◁ₗ uninit LPtr ∗
        local_cur ◁ₗ (l1_suffix @ (list_t)) ∗
        arg_l2 ◁ₗ (p @ (&own (cur_l2 @ (list_t)))) ∗
        arg_l1 ◁ₗ (uninit (LPtr)) ∗
        ⌜cur_l2 = l1_prefix ++ l2⌝ ∗
        ⌜l1 = rev l1_prefix ++ l1_suffix⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "rev_append" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "rev_append" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "rev_append".
  Qed.
End proof_rev_append.
