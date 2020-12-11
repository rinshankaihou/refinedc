From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_argtest.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [argtest]. *)
  Lemma type_argtest (global_blue global_getblue : loc) :
    global_blue ◁ᵥ global_blue @ function_ptr type_of_blue -∗
    global_getblue ◁ᵥ global_getblue @ function_ptr type_of_getblue -∗
    typed_function (impl_argtest global_blue global_getblue) type_of_argtest.
  Proof.
    start_function "argtest" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "argtest" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "argtest".
  Qed.
End proof_argtest.
