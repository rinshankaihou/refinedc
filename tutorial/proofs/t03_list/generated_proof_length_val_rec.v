From refinedc.typing Require Import typing.
From refinedc.tutorial.t03_list Require Import generated_code.
From refinedc.tutorial.t03_list Require Import generated_spec.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [tutorial/t03_list.c]. *)
Section proof_length_val_rec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [length_val_rec]. *)
  Lemma type_length_val_rec (global_length_val_rec : loc) :
    global_length_val_rec ◁ᵥ global_length_val_rec @ function_ptr type_of_length_val_rec -∗
    typed_function (impl_length_val_rec global_length_val_rec) type_of_length_val_rec.
  Proof.
    Local Open Scope printing_sugar.
    start_function "length_val_rec" ([v l]) => arg_p.
    prepare_parameters (v l).
    split_blocks ((
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "length_val_rec" "#0".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "length_val_rec".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "length_val_rec".
  Qed.
End proof_length_val_rec.
