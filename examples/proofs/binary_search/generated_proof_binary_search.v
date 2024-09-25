From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_binary_search.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Typing proof for [binary_search]. *)
  Lemma type_binary_search :
    ⊢ typed_function impl_binary_search type_of_binary_search.
  Proof.
    Local Open Scope printing_sugar.
    start_function "binary_search" ([[[[[R ls] x] p] ty] px]) => arg_comp arg_xs arg_n arg_x local_r local_l local_k.
    prepare_parameters (R ls x p ty px).
    split_blocks ((
      <[ "#1" :=
        ∃ vl : nat,
        ∃ vr : nat,
        arg_comp ◁ₗ (function_ptr (fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ builtin_boolean; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝)) ∗
        arg_xs ◁ₗ (p @ (&own (array (void*) ((fun x => (x.1 @ &own (ty x.2)) : type) <$> ls)))) ∗
        arg_n ◁ₗ ((length ls) @ (int (size_t))) ∗
        arg_x ◁ₗ (px @ (&own (ty x))) ∗
        local_k ◁ₗ uninit (it_layout size_t) ∗
        local_l ◁ₗ (vl @ (int (size_t))) ∗
        local_r ◁ₗ (vr @ (int (size_t))) ∗
        ⌜vl <= vr⌝ ∗
        ⌜vr <= length ls⌝ ∗
        ⌜∀ i y, (i < vl)%nat → ls.*2 !! i = Some y → R y x⌝ ∗
        ⌜∀ i y, (vr ≤ i)%nat → ls.*2 !! i = Some y → ¬ R y x⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) (
      @nil Prop
    ).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "binary_search" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "binary_search" "#1".
    Unshelve. all: unshelve_sidecond; sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by [revert select (∀ i j, _ → _ → ¬ R _ _); apply; [|apply list_lookup_fmap_Some; naive_solver]; solve_goal].
    all: try by apply: binary_search_cond_1; [solve_goal|..]; solve_goal.
    all: try by apply: binary_search_cond_2; [solve_goal|..]; solve_goal.
    all: print_sidecondition_goal "binary_search".
    Unshelve. all: try done; try apply: inhabitant; print_remaining_shelved_goal "binary_search".
  Qed.
End proof_binary_search.
