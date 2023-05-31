From lithium Require Export base.

(** This file collects all Ltac hooks that Lithium provides. *)

(** [can_solve_hook] is expected to provide a general purpose solver
for pure sideconditions. It should try hard to solve the goal. *)
Ltac can_solve_hook := fail "No can_solve_hook provided!".

(** [normalize_hook] is expected to provide a tactic that should be
used for rewriting based normalization of goals. See also
[normalize.v]. *)
Ltac normalize_hook := fail "No normalize_hook provided!".

(** The [sidecond_hook] and [unsolved_sidecond_hook] hooks that get
called for all sideconditions resp. all sideconditions that are not
automatically solved using the default solver. *)
Ltac sidecond_hook := idtac.
Ltac unsolved_sidecond_hook := idtac.

(** There can be some goals where one should not call injection on an
hypothesis that is introduced. The [check_injection_hook] hook is called
before injection and allows the client to customize this. *)
Ltac check_injection_hook := idtac.
