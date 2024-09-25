From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_safe_exit.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [safe_exit]. *)
  Lemma type_safe_exit :
    ⊢ typed_function impl_safe_exit type_of_safe_exit.
  Proof.
    Local Open Scope printing_sugar.
    start_function "safe_exit" ([]).
    split_blocks ((
      <[ "#1" :=True
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "safe_exit" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "safe_exit" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "safe_exit".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "safe_exit".
  Qed.
End proof_safe_exit.
