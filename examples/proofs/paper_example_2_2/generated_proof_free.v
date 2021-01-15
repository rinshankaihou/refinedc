From refinedc.typing Require Import typing.
From refinedc.examples.paper_example_2_2 Require Import generated_code.
From refinedc.examples.paper_example_2_2 Require Import generated_spec.
From refinedc.examples.spinlock Require Import spinlock_def.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_2.c]. *)
Section proof_free.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!lockG Σ}.

  (* Typing proof for [free]. *)
  Lemma type_free :
    ⊢ typed_function impl_free type_of_free.
  Proof.
    Open Scope printing_sugar.
    start_function "free" ([[[s p] q] n]) => arg_list arg_data arg_size local_cur local_entry.
    split_blocks ((
      <[ "#1" :=
        ∃ cp : loc,
        ∃ cs : gmultiset nat,
        arg_data ◁ₗ (q @ (&own (uninit (n)))) ∗
        arg_size ◁ₗ (n @ (int (size_t))) ∗
        local_entry ◁ₗ uninit void* ∗
        local_cur ◁ₗ (cp @ (&own (cs @ (chunks_t)))) ∗
        arg_list ◁ₗ (p @ (&own (wand (cp ◁ₗ ({[n]} ⊎ cs) @ chunks_t) (({[n]} ⊎ s) @ (chunks_t)))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "free" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: multiset_solver.
    all: print_sidecondition_goal "free".
  Qed.
End proof_free.
