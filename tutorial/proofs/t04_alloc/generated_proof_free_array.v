From refinedc.typing Require Import typing.
From refinedc.tutorial.t04_alloc Require Import generated_code.
From refinedc.tutorial.t04_alloc Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section proof_free_array.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [free_array]. *)
  Lemma type_free_array (global_free : loc) :
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    typed_function (impl_free_array global_free) type_of_free_array.
  Proof.
    Open Scope printing_sugar.
    start_function "free_array" ([size n]) => arg_size arg_n arg_ptr.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free_array" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by rewrite /layout_wf ?Nat2Z.inj_mul ?Z2Nat.id //; repeat apply Z.divide_mul_r.
    all: print_sidecondition_goal "free_array".
  Qed.
End proof_free_array.
