From refinedc.typing Require Import typing.
From refinedc.examples.tests Require Import generated_code.
Set Default Proof Using "Type".

(* Generated from [examples/tests.c]. *)
Section spec.
  Context `{!typeG Σ} `{!globalG Σ}.

  (* Type definitions. *)

  (* Specifications for function [test1]. *)
  Definition type_of_test1 :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [return1]. *)
  Definition type_of_return1 :=
    fn(∀ () : (); True) → ∃ () : (), ((1) @ (int (i32))); True.

  (* Specifications for function [unreachable]. *)
  Definition type_of_unreachable :=
    fn(∀ () : (); ⌜False⌝) → ∃ () : (), (void); True.

  (* Specifications for function [test_ternary]. *)
  Definition type_of_test_ternary :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [test_bits]. *)
  Definition type_of_test_bits :=
    fn(∀ () : (); True) → ∃ () : (), (void); True.

  (* Specifications for function [test_comma]. *)
  Definition type_of_test_comma :=
    fn(∀ () : (); True) → ∃ () : (), ((0) @ (int (i32))); True.

  (* Specifications for function [inline_global2]. *)
  Definition type_of_inline_global2 :=
    fn(∀ () : (); (initialized "global" ()))
      → ∃ () : (), ((1) @ (int (i32))); True.
End spec.
