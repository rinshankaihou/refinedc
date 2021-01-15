From refinedc.typing Require Import typing.
From refinedc.tutorial.t02_pointers Require Import generated_code.
From refinedc.tutorial.t02_pointers Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_pointers.c]. *)
Section proof_ptr_id_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [ptr_id_test]. *)
  Lemma type_ptr_id_test (global_ptr_id : loc) :
    global_ptr_id ◁ᵥ global_ptr_id @ function_ptr type_of_ptr_id -∗
    typed_function (impl_ptr_id_test global_ptr_id) type_of_ptr_id_test.
  Proof.
    Open Scope printing_sugar.
    start_function "ptr_id_test" ([]) => local_x.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "ptr_id_test" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "ptr_id_test".
  Qed.
End proof_ptr_id_test.
