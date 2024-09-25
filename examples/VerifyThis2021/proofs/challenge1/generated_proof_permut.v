From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge1 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge1 Require Import generated_spec.
From refinedc.examples.VerifyThis2021.challenge1 Require Import challenge1_lemmas.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge1.c]. *)
Section proof_permut.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [permut]. *)
  Lemma type_permut (global_copy_array global_list_new global_list_snoc global_next global_sort : loc) :
    global_copy_array ◁ᵥ global_copy_array @ function_ptr type_of_copy_array -∗
    global_list_new ◁ᵥ global_list_new @ function_ptr type_of_list_new -∗
    global_list_snoc ◁ᵥ global_list_snoc @ function_ptr type_of_list_snoc -∗
    global_next ◁ᵥ global_next @ function_ptr type_of_next -∗
    global_sort ◁ᵥ global_sort @ function_ptr type_of_sort -∗
    typed_function (impl_permut global_copy_array global_list_new global_list_snoc global_next global_sort) type_of_permut.
  Proof.
    Local Open Scope printing_sugar.
    start_function "permut" ([p A]) => arg_A arg_size local_copy local_l.
    prepare_parameters (p A).
    split_blocks ((
      <[ "#2" :=
        ∃ ps : list (list Z),
        ∃ Acur : list Z,
        arg_size ◁ₗ ((length A) @ (int (i32))) ∗
        local_copy ◁ₗ uninit void* ∗
        local_l ◁ₗ (((λ p, (array i32 (p `at_type` int i32))) <$> ps) @ (list_t)) ∗
        arg_A ◁ₗ (p @ (&own (array (i32) (Acur `at_type` int i32)))) ∗
        ⌜∀ i p1 p2, ps !! i = Some p1 → ps !! (S i) = Some p2 → next_perm p1 (Some p2)⌝ ∗
        ⌜last ps = Some Acur⌝ ∗
        ⌜length Acur = length A⌝ ∗
        ⌜0 < length A⌝ ∗
        ⌜∃ Ahead, head ps = Some Ahead ∧ Ahead ≡ₚ A ∧ Sorted Z.le Ahead⌝ ∗
        ⌜length Acur = length A⌝ ∗
        ⌜0 < length A⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "permut" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "permut" "#2".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by apply: Permutation_length.
    all: try by destruct ps => //; simplify_eq/=; naive_solver.
    all: try by apply: all_perms.
    all: try by apply: perms_no_dup.
    all: try by apply: last_snoc.
    all: try by revert select (next_perm _ (Some _)) => /next_perm_implies_perm/Permutation_length; lia.
    all: case_bool_decide; [case_bool_decide; [naive_solver |lia] | ].
    all: revert select ([_] !! _ = _) => /list_lookup_singleton_Some[??]; subst.
    all: case_bool_decide; [| lia]; simplify_eq.
    all: have Heq : ps !! i = last ps by rewrite last_lookup; f_equal; lia.
    all: rewrite ->Heq in *; by simplify_eq.
    all: print_sidecondition_goal "permut".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "permut".
  Qed.
End proof_permut.
