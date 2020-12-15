From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_set_blue.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [set_blue]. *)
  Lemma type_set_blue :
    ⊢ typed_function impl_set_blue type_of_set_blue.
  Proof.
    start_function "set_blue" ([[p c] b]) => arg_c arg_b.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "set_blue" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "set_blue".
  Qed.
End proof_set_blue.
