From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_test_manual_exist_arg_client.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_manual_exist_arg_client]. *)
  Lemma type_test_manual_exist_arg_client (global_test_manual_exist_arg : loc) :
    global_test_manual_exist_arg ◁ᵥ global_test_manual_exist_arg @ function_ptr type_of_test_manual_exist_arg -∗
    typed_function (impl_test_manual_exist_arg_client global_test_manual_exist_arg) type_of_test_manual_exist_arg_client.
  Proof.
    Local Open Scope printing_sugar.
    start_function "test_manual_exist_arg_client" ([]) => local_x.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      IPROP_HINT (ASSERT_COND "1") (λ _ : (),
        
        (set_lvar "k" 4)
        )%I ::
      IPROP_HINT (ASSERT_COND "0") (λ x_val : Z,
        
        local_x ◁ₗ (x_val @ (int (i32))) ∗
        (set_lvar "k" x_val)
        )%I ::
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_manual_exist_arg_client" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_manual_exist_arg_client".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "test_manual_exist_arg_client".
  Qed.
End proof_test_manual_exist_arg_client.
