From refinedc.typing Require Import typing.
From refinedc.examples.binary_search Require Import generated_code.
From caesium Require Import builtins_specs.
From refinedc.typing Require Import malloc.
From refinedc.examples.binary_search Require Import binary_search_extra.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.
  Context `{!mallocG Σ}.

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [safe_exit]. *)
  Definition type_of_safe_exit :=
    fn(∀ () : (); True) → ∃ () : (), (void); ⌜False⌝.

  (* Specifications for function [malloc]. *)
  Definition type_of_malloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (optionalO (λ _ : unit,
        &own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))
      ) (null)); True.

  (* Specifications for function [free]. *)
  Definition type_of_free :=
    fn(∀ n : Z; (&own (malloced_early (n) (uninit (ly_max_align (Z.to_nat n))))); True)
      → ∃ () : (), (void); True.

  (* Specifications for function [xmalloc]. *)
  Definition type_of_xmalloc :=
    fn(∀ n : Z; (n @ (int (size_t))); True)
      → ∃ () : (), (&own (malloced (n) (uninit (ly_max_align (Z.to_nat n))))); True.

  (* Specifications for function [binary_search]. *)
  Definition type_of_binary_search :=
    fn(∀ (R, ls, x, p, ty, px) : (Z → Z → Prop) * (list (loc * Z)) * Z * loc * (Z → type) * loc; (function_ptr (fn(∀ (x, y, px, py) : (Z * Z * loc * loc); px @ &own (ty x), py @ &own (ty y); True) → ∃ (b) : (bool), b @ builtin_boolean; px ◁ₗ ty x ∗ py ◁ₗ ty y ∗ ⌜b ↔ R x y⌝)), (p @ (&own (array (void*) ((fun x => (x.1 @ &own (ty x.2)) : type) <$> ls)))), ((length ls) @ (int (size_t))), (px @ (&own (ty x))); ⌜StronglySorted R ls.*2⌝ ∗ ⌜Transitive R⌝)
      → ∃ n : nat, (n @ (int (size_t))); ⌜∀ i y, (i < n)%nat → ls.*2 !! i = Some y → R y x⌝ ∗ ⌜∀ i y, (n ≤ i)%nat → ls.*2 !! i = Some y → ¬ R y x⌝ ∗ (p ◁ₗ (array (void*) ((fun x => (x.1 @ &own (ty x.2)) : type) <$> ls))) ∗ (px ◁ₗ (ty (x))).

  (* Specifications for function [compare_int]. *)
  Definition type_of_compare_int :=
    fn(∀ (x, y, px, py) : Z * Z * loc * loc; (px @ (&own (x @ (int (size_t))))), (py @ (&own (y @ (int (size_t))))); True)
      → ∃ b : bool, (b @ (builtin_boolean)); (px ◁ₗ (x @ (int (size_t)))) ∗ (py ◁ₗ (y @ (int (size_t)))) ∗ ⌜b ↔ Z.le x y⌝.

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); ⌜True⌝) → ∃ () : (), (void); True.
End spec.
