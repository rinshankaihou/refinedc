From refinedc.typing Require Import typing.
From refinedc.tutorial.t07_arrays Require Import generated_code.
From refinedc.tutorial.t07_arrays Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.tutorial.t07_arrays Require Import t07_arrays_extra.
Set Default Proof Using "Type".

(* Generated from [tutorial/t07_arrays.c]. *)
Section proof_min_array.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [min_array]. *)
  Lemma type_min_array :
    ⊢ typed_function impl_min_array type_of_min_array.
  Proof.
    Local Open Scope printing_sugar.
    start_function "min_array" ([[ar elts] n]) => arg_ar arg_n local_i local_res.
    prepare_parameters (ar elts n).
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
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min_array" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min_array" "#2".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: index_of_min_list_Z_take_1; solve_goal.
    all: try by apply: index_of_min_list_Z_take_last; solve_goal.
    all: try by apply: index_of_min_list_Z_take_not_last; solve_goal.
    all: try (rewrite list_lookup_fmap H8; solve_goal).
    all: try (assert (i = n) by lia; solve_goal).
    all: print_sidecondition_goal "min_array".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "min_array".
  Qed.
End proof_min_array.
