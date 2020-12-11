From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_init_int_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int_test]. *)
  Lemma type_init_int_test (global_init_int : loc) :
    global_init_int ◁ᵥ global_init_int @ function_ptr type_of_init_int -∗
    typed_function (impl_init_int_test global_init_int) type_of_init_int_test.
  Proof.
    start_function "init_int_test" (p) => arg_out local_i.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "init_int_test" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_int_test".
  Qed.
End proof_init_int_test.
