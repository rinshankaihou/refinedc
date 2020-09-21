From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import code.
From refinedc.examples.btree Require Import spec.
From refinedc.examples.btree Require Import btree_extra.
From refinedc.examples.btree Require Import btree_learn.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section proof_key_index.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [key_index]. *)
  Lemma type_key_index :
    ⊢ typed_function impl_key_index type_of_key_index.
  Proof.
    start_function "key_index" ([[[[p l] n] k] sz]) => arg_ar arg_n arg_k local_slot.
    split_blocks ((
      <[ "#1" :=
        ∃ s : nat,
        arg_ar ◁ₗ (p @ (&own (array (it_layout i32) ((l `at_type` int i32) ++ replicate (sz - n)%nat (uninit i32 : type))))) ∗
        arg_n ◁ₗ (n @ (int (i32))) ∗
        arg_k ◁ₗ (k @ (int (i32))) ∗
        local_slot ◁ₗ (s @ (int (i32))) ∗
        ⌜∀ i : nat, ∀ v : Z, i < s → l !! i = Some v → v < k⌝ ∗
        ⌜s ≤ length l⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "key_index" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "key_index" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    + destruct (decide (i = s)); by naive_solver lia.
    + move: (elem_of_list_lookup_1 _ _ H14) => [i Hi]. destruct (decide (y = k)); [ done | exfalso ]. assert (k < y) as Hky by lia. assert (i < s)%nat as Hle by by eapply StronglySorted_lookup_index_lt. assert (i < s) as His  by lia. assert (k < k) by by eapply H0. by lia.
    + apply StronglySorted_insert_drop_take; last done. * move => z Hz. destruct (l !! z) eqn:?; naive_solver lia. * move: (elem_of_list_lookup_2 l s y H7) => Hy. rewrite H7 /=.   assert (k ≠ y); [ by set_solver | by lia ].
    + assert (s = length l) as -> by lia. assert (k < k); last by lia. move: (elem_of_list_lookup_1 _ _ H7) => [i Hi]. move: (lookup_lt_Some _ _ _ Hi) => Hlt. naive_solver lia.
    + assert (s = length l) as -> by lia. rewrite drop_all. apply StronglySorted_app; [ .. | done | by do 2 constructor ]. move => x y Hx Hy. assert (y = k) as -> by set_solver. move: (elem_of_list_lookup_1 _ _ Hx) => [i Hi]. move: (lookup_lt_Some _ _ _ Hi) => Hlt. naive_solver lia.
    all: print_sidecondition_goal "key_index".
  Qed.
End proof_key_index.
