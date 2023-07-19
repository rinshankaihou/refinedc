From lithium.tutorial Require Import lang.

(** The tactic [reshape_expr e tac] decomposes the expression [e] into an
evaluation context [K] and a subexpression [e']. It calls the tactic [tac K e']
for each possible decomposition until [tac] succeeds. *)
Ltac reshape_expr e tac :=
  (* Note that the current context is spread into a list of fully-constructed
     items [K] A fully-constructed item is inserted into [K] by calling
     [add_item]. *)
  let rec go K e :=
    match e with
    | _                               => tac K e
    | App ?e (Val ?v)                 => add_item (AppLCtx v) K e
    | App ?e1 ?e2                     => add_item (AppRCtx e1) K e2
    | UnOp ?op ?e                     => add_item (UnOpCtx op) K e
    | BinOp ?op (Val ?v) ?e           => add_item (BinOpRCtx op v) K e
    | BinOp ?op ?e1 ?e2               => add_item (BinOpLCtx op e2) K e1
    | If ?e0 ?e1 ?e2                  => add_item (IfCtx e1 e2) K e0
    | Assert ?e                       => add_item (AssertCtx) K e
    | Load ?e                         => add_item (LoadCtx) K e
    | Store ?e (Val ?v)               => add_item (StoreLCtx v) K e
    | Store ?e1 ?e2                   => add_item (StoreRCtx e1) K e2
    end
  with add_item Ki K e := go (Ki :: K) e
  in go (@nil ectx_item) e.


Ltac inv_head_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : head_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and should thus better be avoided. *)
     inversion H; subst; clear H
  end.

Create HintDb head_step.
Global Hint Extern 0 (head_reducible _ _) => eexists _, _, _, _; simpl : head_step.

(* [simpl apply] is too stupid, so we need extern hints here. *)
Global Hint Extern 1 (head_step _ _ _ _ _ _) => econstructor : head_step.
Global Hint Extern 0 (head_step Alloc _ _ _ _ _) => apply alloc_fresh : head_step.
