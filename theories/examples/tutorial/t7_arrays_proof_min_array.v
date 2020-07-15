From refinedc.typing Require Import typing.
From refinedc.examples.tutorial Require Import t7_arrays_code.
From refinedc.examples.tutorial Require Import t7_arrays_spec.
From refinedc.examples.tutorial Require Import t7_arrays_extra.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t7_arrays.c]. *)
Section proof_min_array.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [min_array]. *)
  Lemma type_min_array :
    ⊢ typed_function impl_min_array type_of_min_array.
  Proof.
    start_function "min_array" ([[ar elts] n]) => arg_ar arg_n local_i local_res.
    split_blocks ((
      <[ "#2" :=
        ∃ res : nat,
        ∃ i : nat,
        arg_ar ◁ₗ (ar @ (&own (array (i32) (elts `at_type` (int i32))))) ∗
        arg_n ◁ₗ (n @ (int (i32))) ∗
        local_res ◁ₗ (res @ (int (i32))) ∗
        local_i ◁ₗ (i @ (int (i32))) ∗
        ⌜(i ≤ n)%nat⌝ ∗
        ⌜(res < min i n)%nat⌝ ∗
        ⌜(n ≤ length elts)%nat⌝ ∗
        ⌜index_of_min_list_Z (take i elts) res⌝
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min_array" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min_array" "#2".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by apply: index_of_min_list_Z_take_1; solve_goal.
    all: try by apply: index_of_min_list_Z_take_last; solve_goal.
    all: try by apply: index_of_min_list_Z_take_not_last; solve_goal.
    all: try (rewrite list_lookup_fmap H8; solve_goal).
    all: try (assert (i = n) by lia; solve_goal).
    all: print_sidecondition_goal "min_array".
  Qed.
End proof_min_array.
