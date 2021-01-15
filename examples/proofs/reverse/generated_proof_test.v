From refinedc.typing Require Import typing.
From refinedc.examples.reverse Require Import generated_code.
From refinedc.examples.reverse Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [examples/reverse.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_init global_pop global_push : loc) :
    global_init ◁ᵥ global_init @ function_ptr type_of_init -∗
    global_pop ◁ᵥ global_pop @ function_ptr type_of_pop -∗
    global_push ◁ᵥ global_push @ function_ptr type_of_push -∗
    typed_function (impl_test global_init global_pop global_push) type_of_test.
  Proof.
    Open Scope printing_sugar.
    start_function "test" ([]) => local_list local_local1 local_local1_node local_local3 local_local2 local_local4 local_local2_node.
    split_blocks ((
      <[ "#1" :=
        ∃ l1 : loc,
        ∃ l2 : loc,
        ∃ l3 : loc,
        ∃ l4 : loc,
        local_list ◁ₗ uninit void* ∗
        local_local3 ◁ₗ uninit void* ∗
        local_local4 ◁ₗ uninit void* ∗
        local_local1 ◁ₗ (place (l1)) ∗
        local_local1_node ◁ₗ (place (l2)) ∗
        local_local2 ◁ₗ (place (l3)) ∗
        local_local2_node ◁ₗ (place (l4))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.
