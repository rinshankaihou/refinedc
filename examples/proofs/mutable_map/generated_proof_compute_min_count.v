From refinedc.typing Require Import typing.
From refinedc.examples.mutable_map Require Import generated_code.
From refinedc.examples.mutable_map Require Import generated_spec.
From refinedc.examples.mutable_map Require Import mutable_map_extra.
Set Default Proof Using "Type".

(* Generated from [examples/mutable_map.c]. *)
Section proof_compute_min_count.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [compute_min_count]. *)
  Lemma type_compute_min_count :
    ⊢ typed_function impl_compute_min_count type_of_compute_min_count.
  Proof.
    Open Scope printing_sugar.
    start_function "compute_min_count" (n) => arg_len.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "compute_min_count" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "compute_min_count".
  Qed.
End proof_compute_min_count.
