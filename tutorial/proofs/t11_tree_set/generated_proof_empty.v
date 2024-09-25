From refinedc.typing Require Import typing.
From refinedc.tutorial.t11_tree_set Require Import generated_code.
From refinedc.tutorial.t11_tree_set Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t11_tree_set.c]. *)
Section proof_empty.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [empty]. *)
  Lemma type_empty :
    ⊢ typed_function impl_empty type_of_empty.
  Proof.
    Local Open Scope printing_sugar.
    start_function "empty" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "empty" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "empty".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "empty".
  Qed.
End proof_empty.
