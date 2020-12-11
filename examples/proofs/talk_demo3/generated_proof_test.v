From refinedc.typing Require Import typing.
From refinedc.examples.talk_demo3 Require Import generated_code.
From refinedc.examples.talk_demo3 Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo3.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_alloc global_append : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    global_append ◁ᵥ global_append @ function_ptr type_of_append -∗
    typed_function (impl_test global_alloc global_append) type_of_test.
  Proof.
    start_function "test" ([]) => local_node1 local_node2.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.
