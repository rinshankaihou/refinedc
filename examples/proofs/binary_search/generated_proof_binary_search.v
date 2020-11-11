From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import generated_spec.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section proof_binary_search.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Typing proof for [binary_search]. *)
  Lemma type_binary_search :
    ⊢ typed_function impl_binary_search type_of_binary_search.
  Proof.
    start_function "binary_search" ([[[[R ls] x] p] ty]) => arg_xs arg_n arg_x arg_comp local_r local_l local_k.
    split_blocks ((
      <[ "#1" :=
        ∃ vl : nat,
        ∃ vr : nat,
        arg_xs ◁ₗ (p @ (&own (array (LPtr) ((fun x => &own (ty x) : type) <$> ls)))) ∗
        arg_n ◁ₗ ((length ls) @ (int (i32))) ∗
        arg_x ◁ₗ (&own (ty x)) ∗
        arg_comp ◁ₗ (function_ptr (fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ boolean bool_it; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝)) ∗
        local_k ◁ₗ uninit (it_layout i32) ∗
        local_l ◁ₗ (vl @ (int (i32))) ∗
        local_r ◁ₗ (vr @ (int (i32))) ∗
        ⌜vl <= vr⌝ ∗
        ⌜vr <= length ls⌝ ∗
        ⌜∀ i y, (i < vl)%nat → ls !! i = Some y → R y x⌝ ∗
        ⌜∀ i y, (vr ≤ i)%nat → ls !! i = Some y → ¬ R y x⌝
    ]> $
      ∅
    )%I : gmap label (iProp Σ)) ((
      ∅
    )%I : gmap label (iProp Σ)).
    - repeat liRStep; liShow.
      all: print_typesystem_goal "binary_search" "#0".
    - repeat liRStep; liShow.
      all: print_typesystem_goal "binary_search" "#1".
    Unshelve. all: sidecond_hook; prepare_sideconditions; normalize_and_simpl_goal; try solve_goal; unsolved_sidecond_hook.
    all: try by [revert select (∀ i j, _ → _ → ¬ R _ _); apply; [| done];solve_goal].
    all: try by apply: (binary_search_cond_1 y); solve_goal.
    all: try by apply: (binary_search_cond_2 y); solve_goal.
    all: print_sidecondition_goal "binary_search".
  Qed.
End proof_binary_search.
