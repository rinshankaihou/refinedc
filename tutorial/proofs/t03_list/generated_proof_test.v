From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_test.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [test]. *)
  Lemma type_test (global_alloc global_free global_init global_is_empty global_member global_pop global_push global_reverse : loc) :
    global_alloc ◁ᵥ global_alloc @ function_ptr type_of_alloc -∗
    global_free ◁ᵥ global_free @ function_ptr type_of_free -∗
    global_init ◁ᵥ global_init @ function_ptr type_of_init -∗
    global_is_empty ◁ᵥ global_is_empty @ function_ptr type_of_is_empty -∗
    global_member ◁ᵥ global_member @ function_ptr type_of_member -∗
    global_pop ◁ᵥ global_pop @ function_ptr type_of_pop -∗
    global_push ◁ᵥ global_push @ function_ptr type_of_push -∗
    global_reverse ◁ᵥ global_reverse @ function_ptr type_of_reverse -∗
    typed_function (impl_test global_alloc global_free global_init global_is_empty global_member global_pop global_push global_reverse) type_of_test.
  Proof.
    Open Scope printing_sugar.
    start_function "test" ([]) => local_list local_elem2 local_elem1 local_elem3.
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "test" "#0".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by set_unfold; refined_solver.
    all: print_sidecondition_goal "test".
  Qed.
End proof_test.
