From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From refinedc.examples.tagged_ptr Require Import generated_spec.
From refinedc.examples.tagged_ptr Require Import tagged_ptr_extra.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section proof_untag2.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [untag2]. *)
  Lemma type_untag2 (global_copy_alloc_id : loc) :
    global_copy_alloc_id ◁ᵥ global_copy_alloc_id @ inline_function_ptr impl_copy_alloc_id -∗
    typed_function (impl_untag2 global_copy_alloc_id) type_of_untag2.
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
