From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_min.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [min]. *)
  Lemma type_min :
    ⊢ typed_function impl_min type_of_min.
  Proof.
    start_function "min" ([a b]) => arg_a arg_b local_r.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "min" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "min".
  Qed.
End proof_min.
