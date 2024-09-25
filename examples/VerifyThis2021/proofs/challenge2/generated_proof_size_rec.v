From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.VerifyThis2021.challenge2 Require Import defs.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section proof_size_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [size_rec]. *)
  Lemma type_size_rec (global_size_rec : loc) :
    global_size_rec ◁ᵥ global_size_rec @ function_ptr type_of_size_rec -∗
    typed_function (impl_size_rec global_size_rec) type_of_size_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "size_rec" ([v l]) => arg_head.
    prepare_parameters (v l).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "size_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "size_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "size_rec".
  Qed.
End proof_size_rec.
