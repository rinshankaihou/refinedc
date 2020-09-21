From refinedc.typing Require Import typing.
From refinedc.tutorial.quicksort_solution Require Import code.
From refinedc.tutorial.quicksort_solution Require Import spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_solution.c]. *)
Section proof_append.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [append]. *)
  Lemma type_append (append : loc) :
    append ◁ᵥ append @ function_ptr type_of_append -∗
    typed_function (impl_append append) type_of_append.
  Proof.
    start_function "append" ([[p xs] ys]) => arg_l arg_k.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "append" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: print_sidecondition_goal "append".
  Qed.
End proof_append.
