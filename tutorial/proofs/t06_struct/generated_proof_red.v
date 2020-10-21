From refinedc.typing Require Import typing.
From refinedc.tutorial.t06_struct Require Import generated_code.
From refinedc.tutorial.t06_struct Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t06_struct.c]. *)
Section proof_red.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [red]. *)
  Lemma type_red :
    ⊢ typed_function impl_red type_of_red.
  Proof.
    start_function "red" (r) => arg_r local_c.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "red" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "red".
  Qed.
End proof_red.
