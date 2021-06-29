From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_tag_of.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tag_of]. *)
  Lemma type_tag_of :
    ⊢ typed_function impl_tag_of type_of_tag_of.
  Proof.
    Open Scope printing_sugar.
    start_function "tag_of" ([[r ty] v]) => arg_p local_i local_t.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "tag_of" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: rewrite Z_land_add_l; solve_goal.
    all: print_sidecondition_goal "tag_of".
  Qed.
End proof_tag_of.
