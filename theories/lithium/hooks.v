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

(** [enrich_context_hook] can be used to add additional facts to the
context during [solve_goal].  *)
Ltac enrich_context_hook := idtac.

(** [solve_goal_prepare_hook] resp.
[solve_goal_normalized_prepare_hook] are called by [solve_goal] before
resp. after [normalize_and_simpl_goal]. *)
Ltac solve_goal_prepare_hook := idtac.
Ltac solve_goal_normalized_prepare_hook := idtac.
(** [reduce_closed_Z_hook] is called by [solve_goal] to reduce
constant expressions on [Z]. *)
Ltac reduce_closed_Z_hook := idtac.

(** [li_pm_reduce_hook] is an extension point for custom reduction for
IPM terms. *)
Ltac li_pm_reduce_hook H := H.

(** [unfold_instantiated_evar_hook] is called when evar [H] was instantiated. *)
Ltac unfold_instantiated_evar_hook H := idtac.

(** [solve_protected_eq_hook] can be used to unfold definitions before
solving equalities for instantiating evars. *)
Ltac solve_protected_eq_hook := idtac.

(** [liUnfoldLetGoal_hook] allows unfolding custom definitions when
unfolding let-bindings in the goal. *)
Ltac liUnfoldLetGoal_hook H := idtac.

(** [liExtensible_to_i2p_hook] can be used to add custom
judgements to [liExtensible]. *)
Ltac liExtensible_to_i2p_hook P bind cont :=
  fail "No liExtensible_to_i2p_hook provided!".

(** [liExtensible_hook] is called after each successful [liExtensible]. *)
Ltac liExtensible_hook := idtac.

(** [liExist_hook] can be used to override the behavior of [liExist]
for specific types. *)
Ltac liExist_hook A protect := fail "No liExist_hook provided!".

(** [liDestructHint_record_hook] is called on each liDestruct to
record which branch was taken. *)
Ltac liDestructHint_record_hook hint info := idtac.

(** [liToSyntax_hook] is called by [liToSyntax] to (heurisitically)
convert the goal to the Lithium syntax. If one overrides
[liToSyntax_hook] with [fail], conversion to the syntax is disabled. *)
Ltac liToSyntax_hook :=
  idtac.