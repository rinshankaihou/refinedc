From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [binary_search]. *)
  Definition type_of_binary_search :=
    fn(∀ (R, ls, x, p, ty) : (Z → Z → Prop) * (list Z) * Z * loc * (Z → type); (p @ (&own (array (LPtr) ((fun x => &own (ty x) : type) <$> ls)))), ((length ls) @ (int (i32))), (&own (ty x)), (function_ptr (fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ boolean bool_it; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝)); ⌜StronglySorted R ls⌝ ∗ ⌜Transitive R⌝)
      → ∃ n : nat, (n @ (int (i32))); ⌜∀ i y, (i < n)%nat → ls !! i = Some y → R y x⌝ ∗ ⌜∀ i y, (n ≤ i)%nat → ls !! i = Some y → ¬ R y x⌝ ∗ (p ◁ₗ (array (LPtr) ((fun x => &own (ty x) : type) <$> ls))).
End spec.
