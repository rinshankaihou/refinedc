From refinedc.typing Require Import typing.
From refinedc.tutorial.t09_switch Require Import generated_code.
From refinedc.tutorial.t09_switch Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section proof_test_switch_default.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test_switch_default]. *)
  Lemma type_test_switch_default :
    ⊢ typed_function impl_test_switch_default type_of_test_switch_default.
  Proof.
    Open Scope printing_sugar.
    start_function "test_switch_default" (i) => arg_i local_o.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test_switch_default" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test_switch_default".
  Qed.
End proof_test_switch_default.
