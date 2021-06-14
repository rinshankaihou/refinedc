From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_untag.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [untag]. *)
  Lemma type_untag :
    ⊢ typed_function impl_untag type_of_untag.
  Proof.
    Open Scope printing_sugar.
    start_function "untag" ([[r ty] P]) => arg_p local_i.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "untag" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "untag".
  Qed.
End proof_untag.
