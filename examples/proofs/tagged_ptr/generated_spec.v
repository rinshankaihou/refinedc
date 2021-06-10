From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Notation TAG_MOD := (8%nat) (only parsing).

  (* Type definitions. *)

  (* Specifications for function [tag_of]. *)
  Definition type_of_tag_of :=
    fn(∀ (r, ty, v) : (loc * Z) * type * val; (value (void*) (v)); (v ◁ᵥ (r @ (tagged_ptr (Own) (TAG_MOD) (ty)))))
      → ∃ () : (), ((r.2) @ (int (u8))); ⌜0 ≤ r.2 < TAG_MOD⌝ ∗ (v ◁ᵥ (r @ (tagged_ptr (Own) (TAG_MOD) (ty)))).

  (* Specifications for function [tag]. *)
  Definition type_of_tag :=
    fn(∀ (r, t, ty) : (loc * Z) * Z * type; (r @ (tagged_ptr (Own) (TAG_MOD) (ty))), (t @ (int (u8))); ⌜0 ≤ t < TAG_MOD⌝)
      → ∃ () : (), (((r.1, t)) @ (tagged_ptr (Own) (TAG_MOD) (ty))); True.

  (* Specifications for function [untag]. *)
  Definition type_of_untag :=
    fn(∀ (r, ty) : (loc * Z) * type; (r @ (tagged_ptr (Own) (TAG_MOD) (ty))); True)
      → ∃ () : (), ((r.1) @ (&own (ty))); True.

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (size_t))); True.

  (* Specifications for function [is_aligned]. *)
  Definition type_of_is_aligned :=
    fn(∀ (l, beta, n) : loc * own_state * Z; (l @ (&frac{beta} (n @ (int (i32))))); True)
      → ∃ () : (), ((bool_decide (l `aligned_to` 8%nat)) @ (boolean (i32))); (l ◁ₗ{beta} (n @ (int (i32)))).
End spec.
