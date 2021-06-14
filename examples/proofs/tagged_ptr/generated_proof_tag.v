From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_tag.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [tag]. *)
  Lemma type_tag (global_tag_of : loc) :
    global_tag_of ◁ᵥ global_tag_of @ function_ptr type_of_tag_of -∗
    typed_function (impl_tag global_tag_of) type_of_tag.
  Proof.
    Open Scope printing_sugar.
    start_function "tag" ([[[r t] ty] P]) => arg_p arg_t local_old_t.
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
