From refinedc.typing Require Import typing.
From refinedc.tutorial.t01_basic Require Import generated_code.
From refinedc.tutorial.t01_basic Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t01_basic.c]. *)
Section proof_init_int.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [init_int]. *)
  Lemma type_init_int :
    ⊢ typed_function impl_init_int type_of_init_int.
  Proof.
    Local Open Scope printing_sugar.
    start_function "init_int" (p) => arg_out.
    prepare_parameters (p).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
      repeat liRStep; liShow.
      all: print_typesystem_goal "init_int" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "init_int".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "init_int".
  Qed.
End proof_init_int.
