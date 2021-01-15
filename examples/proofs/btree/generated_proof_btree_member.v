From refinedc.typing Require Import typing.
From refinedc.examples.btree Require Import generated_code.
From refinedc.examples.btree Require Import generated_spec.
From refinedc.examples.btree Require Import btree_extra.
From refinedc.examples.btree Require Import btree_learn.
Set Default Proof Using "Type".

(* Generated from [examples/btree.c]. *)
Section proof_btree_member.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [btree_member]. *)
  Lemma type_btree_member (global_key_index : loc) :
    global_key_index ◁ᵥ global_key_index @ function_ptr type_of_key_index -∗
    typed_function (impl_btree_member global_key_index) type_of_btree_member.
  Proof.
    Open Scope printing_sugar.
    start_function "btree_member" ([[[p h] m] k]) => arg_t arg_k local_i local_cur.
    split_blocks ((
      <[ "#1" :=
        ∃ cur_p : loc,
        ∃ cur_m : gmap Z type,
        ∃ b : bool,
        ∃ cur_h : nat,
        ∃ min_k : Z,
        ∃ max_k : Z,
        arg_k ◁ₗ (k @ (int (i32))) ∗
        local_i ◁ₗ uninit (it_layout i32) ∗
        local_cur ◁ₗ (cur_p @ (&own ((BR b cur_h min_k max_k cur_m) @ (btree_t)))) ∗
        arg_t ◁ₗ (p @ (&own (wand (cur_p ◁ₗ  ((BR b cur_h min_k max_k cur_m) @ (btree_t)) ) ((BRroot h m) @ (btree_t))))) ∗
        ⌜min_k ≤ k ∧ k ≤ max_k⌝ ∗
        ⌜m !! k = cur_m !! k⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "btree_member" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "btree_member" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    + unfold btree_invariant in *; by solve_goal.
    + rewrite H1; by apply: (btree_invariant_in_keys_not_None H2).
    + by rewrite list_insert_id.
    + apply: (btree_invariant_in_range_child H2); naive_solver lia.
    + rewrite H1; apply: (btree_invariant_lookup_child H2); by naive_solver.
    + do 2 rewrite list_insert_id //; by destruct y0.
    + assert (k ∉ x0) as Hx1. { move => /H7 Hk. apply lookup_lt_Some in Hk. lia. } apply: (btree_invariant_in_range_child H2); by naive_solver.
    + assert (k ∉ x0) as Hx1. { move => /H7 Hk. apply lookup_lt_Some in Hk. lia. } rewrite H1. apply: (btree_invariant_lookup_child H2); by naive_solver.
    + rewrite list_insert_id //; by destruct y.
    all: print_sidecondition_goal "btree_member".
  Qed.
End proof_btree_member.
