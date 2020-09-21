From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import code.
From refinedc.tutorial.t04_alloc Require Import spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_alloc_array.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [alloc_array]. *)
  Lemma type_alloc_array (alloc : loc) :
    alloc ◁ᵥ alloc @ function_ptr type_of_alloc -∗
    typed_function (impl_alloc_array alloc) type_of_alloc_array.
  Proof.
    start_function "alloc_array" ([size n]) => arg_size arg_n.
    split_blocks ((
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "alloc_array" "#0".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: try by rewrite /layout_wf ?Nat2Z.inj_mul ?Z2Nat.id //; repeat apply Z.divide_mul_r.
    all: print_sidecondition_goal "alloc_array".
  Qed.
End proof_alloc_array.
