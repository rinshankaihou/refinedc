From refinedc.typing Require Import typing.
From refinedc.examples.pointers Require Import generated_code.
From refinedc.examples.pointers Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/pointers.c]. *)
Section proof_no_alias.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [no_alias]. *)
  Lemma type_no_alias :
    ⊢ typed_function impl_no_alias type_of_no_alias.
  Proof.
    Local Open Scope printing_sugar.
    start_function "no_alias" ([p q]) => arg_a arg_b local_old_b.
    prepare_parameters (p q).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "no_alias" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "no_alias".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "no_alias".
  Qed.
End proof_no_alias.
