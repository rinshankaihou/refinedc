From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Definition alloc_initialized := initialized "allocator_state" ().

  (* Type definitions. *)

  (* Specifications for function [alloc]. *)
  Definition type_of_alloc :=
    fn(∀ size : nat; (size @ (int (size_t))); ⌜size + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (uninit (Layout size 3))); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ size : nat; (size @ (int (size_t))), (&own (uninit (Layout size 3))); (alloc_initialized) ∗ ⌜(8 | size)⌝)
      → ∃ () : (), (void); True.

  (* Specifications for function [alloc_array]. *)
  Definition type_of_alloc_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))); ⌜size * n + 16 ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); True.

  (* Specifications for function [free_array]. *)
  Definition type_of_free_array :=
    fn(∀ (size, n) : nat * nat; (size @ (int (size_t))), (n @ (int (size_t))), (&own (array (Layout size 3) (replicate n (uninit (Layout size 3))))); ⌜size * n ≤ max_int size_t⌝ ∗ ⌜(8 | size)⌝ ∗ (alloc_initialized))
      → ∃ () : (), (void); True.

  (* Specifications for function [binary_search]. *)
  Definition type_of_binary_search :=
    fn(∀ (R, ls, x, p, ty, px) : (Z → Z → Prop) * (list Z) * Z * loc * (Z → type) * loc; (function_ptr (fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ boolean bool_it; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝)), (p @ (&own (array (LPtr) ((fun x => &own (ty x) : type) <$> ls)))), ((length ls) @ (int (i32))), (px @ (&own (ty x))); ⌜StronglySorted R ls⌝ ∗ ⌜Transitive R⌝)
      → ∃ n : nat, (n @ (int (i32))); ⌜∀ i y, (i < n)%nat → ls !! i = Some y → R y x⌝ ∗ ⌜∀ i y, (n ≤ i)%nat → ls !! i = Some y → ¬ R y x⌝ ∗ (p ◁ₗ (array (LPtr) ((fun x => &own (ty x) : type) <$> ls))) ∗ (px ◁ₗ (ty x)).

  (* Specifications for function [compare_int]. *)
  Definition type_of_compare_int :=
    fn(∀ (x, y, px, py) : Z * Z * loc * loc; (px @ (&own (x @ (int (size_t))))), (py @ (&own (y @ (int (size_t))))); True)
      → ∃ b : bool, (b @ (boolean (bool_it))); (px ◁ₗ (x @ (int (size_t)))) ∗ (py ◁ₗ (y @ (int (size_t)))) ∗ ⌜b ↔ Z.le x y⌝.

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); (alloc_initialized)) → ∃ () : (), (void); True.
End spec.
