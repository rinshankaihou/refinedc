From refinedc.typing Require Export programs type int function uninit own struct optional singleton fixpoint automation padded exist immovable constrained union array wand globals tyfold atomic_bool zeroed.

(* need to be Qpaue, otherwise search for subtyping in malloc1 loops *)
Typeclasses Opaque uninit.

Notation "'block{' n }" := (typed_block _ n _ _ _ _) (only printing, format "'block{'  n  }") : bi_scope.
