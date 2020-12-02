From refinedc.lang Require Import notation tactics.
Set Default Proof Using "Type".

Definition WrappingAdd (it1 it2 : int_type) (es : list expr) : expr :=
  match es with
  | [e1 ; e2] => e1 +{IntOp it1, IntOp it2} e2
  | _ => Val VOID
  end%E.

Program Instance WrappingAdd_wf it1 it2 : MacroWfSubst (WrappingAdd it1 it2).
Next Obligation. move => ???? [|?[|?[|??]]]//. Qed.

Typeclasses Opaque WrappingAdd.
