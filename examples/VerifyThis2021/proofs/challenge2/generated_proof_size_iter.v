From refinedc.typing Require Import typing.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_code.
From refinedc.examples.VerifyThis2021.challenge2 Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.examples.VerifyThis2021.challenge2 Require Import defs.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section proof_size_iter.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [size_iter]. *)
  Lemma type_size_iter :
    ⊢ typed_function impl_size_iter type_of_size_iter.
  Proof.
    Local Open Scope printing_sugar.
    start_function "size_iter" ([v l]) => arg_head local_len.
    prepare_parameters (v l).
    split_blocks ((
      <[ "#1" :=
        ∃ v2 : val,
        ∃ l1 : list Z,
        arg_head ◁ₗ (own_constrained (nonshr_constraint (v2 ◁ᵥ l1 @ list_t)) (value (PtrOp) (v2))) ∗
        local_len ◁ₗ ((length l - length l1) @ (int (size_t))) ∗
        (v ◁ᵥ (wand_val (void*) (v2 ◁ᵥ l1 @ list_t) (l @ (list_t))))
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "size_iter" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "size_iter" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: print_sidecondition_goal "size_iter".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "size_iter".
  Qed.
End proof_size_iter.
