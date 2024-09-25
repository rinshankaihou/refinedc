From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_rc_assert.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_rc_assert]. *)
  Lemma type_test_rc_assert :
    ⊢ typed_function impl_test_rc_assert type_of_test_rc_assert.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_rc_assert" (i) => arg_i.
    prepare_parameters (i).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (ASSERT_COND "1") (λ j : Z,
        
        arg_i ◁ₗ (j @ (int (i32)))
        )%I ::
      IPROP_HINT (ASSERT_COND "0") (λ patt__ : Z * Z,
        let j := patt__.1 in
        let k := patt__.2 in
        
        arg_i ◁ₗ (j @ (int (i32))) ∗
        ⌜k = j⌝
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_rc_assert" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_rc_assert".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_rc_assert".
  Qed.
End proof_test_rc_assert.
