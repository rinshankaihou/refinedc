From refinedc.typing Require Import automation.

Ltac sidecond_hook ::= match goal with |- _ => idtac "SIDECOND" end.
Ltac unsolved_sidecond_hook := match goal with |- _ => idtac "UNSOLVEDSIDECOND" end.
Ltac unfold_instantiated_evar_hook H ::= idtac "EVAR".
Ltac extensible_judgment_hook ::= idtac "EXTENSIBLE".
