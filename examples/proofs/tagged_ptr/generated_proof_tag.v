From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_tag.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tag]. *)
  Lemma type_tag :
    ⊢ typed_function impl_tag type_of_tag.
  Proof.
    Open Scope printing_sugar.
    start_function "tag" ([[r t] ty]) => arg_p arg_t local_i local_new_i local_q.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tag" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "tag".
  Qed.
End proof_tag.
