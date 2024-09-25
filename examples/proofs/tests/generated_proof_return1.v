From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
From refinedc.examples.tests Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section proof_return1.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [return1]. *)
  Lemma type_return1 :
    ⊢ typed_function impl_return1 type_of_return1.
  Proof.
    Local Open Scope printing_sugar.
    start_function "return1" ([]).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "return1" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "return1".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "return1".
  Qed.
End proof_return1.
