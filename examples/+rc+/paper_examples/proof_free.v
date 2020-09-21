From refinedc.typing Require Import typing.
From refinedc.examples.paper_examples Require Import code.
From refinedc.examples.paper_examples Require Import spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_examples.c]. *)
Section proof_free.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [free]. *)
  Lemma type_free :
    ⊢ typed_function impl_free type_of_free.
  Proof.
    start_function "free" ([[s p] ly]) => arg_list arg_data arg_size local_cur local_entry.
    split_blocks ((
      <[ "#1" :=
        ∃ cp : loc,
        ∃ cs : gmultiset layout,
        arg_data ◁ₗ (&own (uninit (ly))) ∗
        arg_size ◁ₗ ((ly.(ly_size)) @ (int (size_t))) ∗
        local_entry ◁ₗ uninit LPtr ∗
        local_cur ◁ₗ (cp @ (&own (cs @ (chunks_t)))) ∗
        arg_list ◁ₗ (p @ (&own (wand (cp ◁ₗ ({[ly]} ⊎ cs) @ chunks_t) (({[ly]} ⊎ s) @ (chunks_t)))))
    ]> $
      ∅
    )%I : gmap block_id (iProp Σ)) ((
      ∅
    )%I : gmap block_id (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free" "#1".
    Unshelve. all: prepare_sideconditions; normalize_and_simpl_goal; try solve_goal.
    all: multiset_solver.
    all: print_sidecondition_goal "free".
  Qed.
End proof_free.
