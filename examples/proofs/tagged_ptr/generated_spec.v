From refinedc.typing Require Import typing.
From refinedc.examples.tagged_ptr Require Import generated_code.
From caesium Require Import builtins_specs.
Set Default Proof Using "Type".

(* Generated from [examples/tagged_ptr.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Inlined code. *)

  Notation TAG_MOD := (8%nat) (only parsing).

  (* Specifications for function [__builtin_ffsll]. *)
  Definition type_of___builtin_ffsll :=
    fn(∀ x : Z; (x @ (int (u64))); True)
      → ∃ () : (), (((Z_least_significant_one x + 1)%Z) @ (int (i32))); True.

  (* Specifications for function [tag_of]. *)
  Definition type_of_tag_of :=
    fn(∀ (r, ty, v) : (loc * Z) * type * val; (at_value (v) (r @ (&tagged (TAG_MOD) (ty)))); (type_alive_own ty))
      → ∃ () : (), ((r.2) @ (int (u8))); (v ◁ᵥ (r @ (&tagged (TAG_MOD) (ty)))) ∗ ⌜0 ≤ r.2 < TAG_MOD⌝.

  (* Specifications for function [tag]. *)
  Definition type_of_tag :=
    fn(∀ (r, t, ty) : (loc * Z) * Z * type; (r @ (&tagged (TAG_MOD) (ty))), (t @ (int (u8))); ⌜0 ≤ t < TAG_MOD⌝ ∗ (type_alive_own ty))
      → ∃ () : (), (((r.1, t)) @ (&tagged (TAG_MOD) (ty))); True.

  (* Specifications for function [untag]. *)
  Definition type_of_untag :=
    fn(∀ (r, ty) : (loc * Z) * type; (r @ (&tagged (TAG_MOD) (ty))); (type_alive_own ty))
      → ∃ () : (), ((r.1) @ (&own (ty))); True.

  (* Specifications for function [untag2]. *)
  Definition type_of_untag2 :=
    fn(∀ (r, ty) : (loc * Z) * type; (r @ (&tagged (TAG_MOD) (ty))); (type_alive_own ty))
      → ∃ () : (), ((r.1) @ (&own (ty))); True.

  (* Specifications for function [test]. *)
  Definition type_of_test :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (size_t))); True.

  (* Specifications for function [is_aligned]. *)
  Definition type_of_is_aligned :=
    fn(∀ (l, n) : loc * Z; (l @ (&own (n @ (int (i32))))); True)
      → ∃ () : (), ((bool_decide (l `aligned_to` 8%nat)) @ (boolean (i32))); (l ◁ₗ (n @ (int (i32)))).
End spec.
