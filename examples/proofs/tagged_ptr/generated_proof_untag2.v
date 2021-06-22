From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_untag2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [untag2]. *)
  Lemma type_untag2 :
    ⊢ typed_function impl_untag2 type_of_untag2.
  Proof.
    Open Scope printing_sugar.
    start_function "untag2" ([r ty]) => arg_p local_i.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "untag2" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "untag2".
  Qed.
End proof_untag2.
