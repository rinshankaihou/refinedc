From stdpp Require Export strings binders.
From lithium Require Export base.
From iris.algebra Require Export ofe.
From iris.program_logic Require Export language ectx_language ectxi_language.

Open Scope Z.

(* This language is inspired by simp-lang: https://github.com/tchajed/iris-simp-lang *)

Record loc : Set := Loc { loc_val : Z }.
Global Instance loc_inhabited : Inhabited loc := populate (Loc inhabitant).
Global Instance loc_eq_dec : EqDecision loc.
Proof. solve_decision. Defined.
Global Instance loc_countable : Countable loc.
Proof. refine (inj_countable' loc_val Loc _). intros []; eauto. Qed.

Inductive base_lit :=
  | LitNULL
  | LitInt (n : Z)
  | LitBool (b : bool)
  | LitLoc (l : loc).

Inductive bin_op :=
  | PlusOp
  | MinusOp
  | EqOp
  | PairOp.

Inductive un_op :=
  | FstOp
  | SndOp.

Inductive expr :=
  (* Values *)
  | Val (v : val)
  (* Base lambda calculus *)
  | Var (x : string)
  | Rec (f x : binder) (e : expr)
  | App (e1 e2 : expr)
  (* Pure operations *)
  | BinOp (op : bin_op) (e1 e2 : expr)
  | UnOp (op : un_op) (e : expr)
  | If (e0 e1 e2 : expr)
  | Assert (e : expr)
  (* Heap *)
  | Alloc
  | Load (e1 : expr)
  | Store (e1 e2 : expr)
with val :=
  | LitV (l : base_lit)
  | RecV (f x : binder) (e : expr)
  | PairV (v1 v2 : val).

Bind Scope expr_scope with expr.
Bind Scope val_scope with val.

Notation of_val := Val (only parsing).

Definition to_val (e : expr) : option val :=
  match e with
  | Val v => Some v
  | _ => None
  end.

Lemma to_of_val v : to_val (of_val v) = Some v.
Proof. by destruct v. Qed.

Lemma of_to_val e v : to_val e = Some v → of_val v = e.
Proof. destruct e=>//=. by intros [= <-]. Qed.

Global Instance of_val_inj : Inj (=) (=) of_val.
Proof. intros ??. congruence. Qed.

(** Instances *)
Global Instance base_lit_eq_dec : EqDecision base_lit.
Proof. solve_decision. Defined.
Global Instance bin_op_eq_dec : EqDecision bin_op.
Proof. solve_decision. Defined.
Global Instance un_op_eq_dec : EqDecision un_op.
Proof. solve_decision. Defined.
Lemma expr_eq_dec (e1 e2: expr) : Decision (e1 = e2)
with val_eq_dec (v1 v2 : val) : Decision (v1 = v2).
Proof.
  { refine
      (match e1, e2 with
        | Val v, Val v' => cast_if (decide (v = v'))
        | Var x, Var x' => cast_if (decide (x = x'))
        | Rec f x e, Rec f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
        | App e1 e2, App e1' e2' | Store e1 e2, Store e1' e2' =>
          cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))
        | BinOp op e1 e2, BinOp op' e1' e2' =>
          cast_if_and3 (decide (op = op')) (decide (e1 = e1')) (decide (e2 = e2'))
        | If e1 e2 e3, If e1' e2' e3' =>
          cast_if_and3 (decide (e1 = e1')) (decide (e2 = e2')) (decide (e3 = e3'))
        | UnOp op e, UnOp op' e' =>
          cast_if_and (decide (op = op')) (decide (e = e'))
        | Load e, Load e' | Assert e, Assert e' =>
          cast_if  (decide (e = e'))
        | Alloc, Alloc => left _
        | _, _ => right _
        end); solve [ abstract intuition congruence ]. }
  { refine
      (match v1, v2 with
        | LitV l, LitV l' => cast_if (decide (l = l'))
        | RecV f x e, RecV f' x' e' => cast_if_and3 (decide (f = f')) (decide (x = x')) (decide (e = e'))
        | PairV e1 e2, PairV e1' e2' => cast_if_and (decide (e1 = e1')) (decide (e2 = e2'))        | _, _ => right _
        end); try solve [ abstract intuition congruence ]. }
Defined.
Global Instance expr_eq_dec' : EqDecision expr := expr_eq_dec.
Global Instance val_eq_dec' : EqDecision val := val_eq_dec.

(** Evaluation contexts *)
Inductive ectx_item :=
  | AppLCtx (v2 : val)
  | AppRCtx (e1 : expr)
  | BinOpLCtx (op : bin_op) (v2 : val)
  | BinOpRCtx (op : bin_op) (e1 : expr)
  | UnOpCtx (op : un_op)
  | IfCtx (e1 e2 : expr)
  | AssertCtx
  | LoadCtx
  | StoreLCtx (v2 : val)
  | StoreRCtx (e1 : expr).

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | AppLCtx v2 => App e (Val v2)
  | AppRCtx e1 => App e1 e
  | BinOpLCtx op v2 => BinOp op e (Val v2)
  | BinOpRCtx op e1 => BinOp op e1 e
  | UnOpCtx op => UnOp op e
  | IfCtx e1 e2 => If e e1 e2
  | AssertCtx => Assert e
  | LoadCtx => Load e
  | StoreLCtx v2 => Store e (Val v2)
  | StoreRCtx e1 => Store e1 e
  end.

(** Substitution *)
Fixpoint subst (x : string) (v : val) (e : expr)  : expr :=
  match e with
  | Val _ => e
  | Var y => if decide (x = y) then Val v else Var y
  | Rec f y e =>
    Rec f y $ if decide (BNamed x ≠ f ∧ BNamed x ≠ y) then subst x v e else e
  | App e1 e2 => App (subst x v e1) (subst x v e2)
  | BinOp op e1 e2 => BinOp op (subst x v e1) (subst x v e2)
  | UnOp op e => UnOp op (subst x v e)
  | If e0 e1 e2 => If (subst x v e0) (subst x v e1) (subst x v e2)
  | Assert e => Assert (subst x v e)
  | Alloc => Alloc
  | Load e => Load (subst x v e)
  | Store e1 e2 => Store (subst x v e1) (subst x v e2)
  end.

Definition subst' (mx : binder) (v : val) : expr → expr :=
  match mx with BNamed x => subst x v | BAnon => id end.

(** Evaluation *)

Definition bin_op_eval (op : bin_op) (v1 v2: val) : option val :=
  match op with
  | PlusOp => match v1, v2 with
              | LitV (LitInt n1), LitV (LitInt n2) =>
                Some (LitV (LitInt (n1 + n2)))
              | _, _ => None
              end
  | MinusOp => match v1, v2 with
              | LitV (LitInt n1), LitV (LitInt n2) =>
                Some (LitV (LitInt (n1 - n2)))
              | _, _ => None
              end
  | EqOp => match v1, v2 with
              | LitV (LitInt n1), LitV (LitInt n2) =>
                  Some (LitV $ LitBool $ bool_decide (n1 = n2))
              | _, _ => None
              end
  | PairOp => Some (PairV v1 v2)
  end.

Definition un_op_eval (op: un_op) (v: val) : option val :=
  match op, v with
  | FstOp, PairV v1 v2 => Some v1
  | SndOp, PairV v1 v2 => Some v2
  | _, _ => None
  end.

(** state *)
Record state : Type := {
  heap: gmap loc val;
}.

Global Instance state_inhabited : Inhabited state :=
  populate {| heap := inhabitant; |}.
Global Instance val_inhabited : Inhabited val := populate (LitV (LitInt 0)).
Global Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).


Definition state_upd_heap (f: gmap loc val → gmap loc val) (σ: state) : state :=
  {| heap := f σ.(heap) |}.
Global Arguments state_upd_heap _ !_ /.

(** step relation *)
Inductive observation :=.
Lemma observations_empty (κs: list observation) : κs = [].
Proof. by destruct κs as [ | [] ]. Qed.


Inductive head_step : expr → state → list observation → expr → state → list expr → Prop :=
  | RecS f x e σ :
    head_step (Rec f x e) σ [] (Val $ RecV f x e) σ []
  | BetaS f x e1 v2 e' σ :
    e' = subst' x v2 (subst' f (RecV f x e1) e1) →
    head_step (App (Val $ RecV f x e1) (Val v2)) σ [] e' σ []
  | BinOpS op v1 v2 v' σ :
    bin_op_eval op v1 v2 = Some v' →
    head_step (BinOp op (Val v1) (Val v2)) σ [] (Val v') σ []
  | UnOpS op v v' σ :
    un_op_eval op v = Some v' →
    head_step (UnOp op (Val v)) σ [] (Val v') σ []
  | IfS e1 e2 σ b :
    head_step (If (Val $ LitV $ LitBool b) e1 e2) σ [] (if b then e1 else e2) σ []
  | AssertS σ :
    head_step (Assert (Val $ LitV $ LitBool true)) σ [] (Val $ LitV $ LitInt 0) σ []
  | AllocS σ l :
    σ.(heap) !! l = None →
    head_step (Alloc) σ
              []
              (Val $ LitV $ LitLoc l) (state_upd_heap <[l := LitV $ LitInt 0]> σ)
              []
  | LoadS v σ l :
    σ.(heap) !! l = Some v →
    head_step (Load (Val $ LitV $ LitLoc l)) σ
              []
              (Val $ v) σ
              []
  | StoreS v w σ l :
    σ.(heap) !! l = Some v →
    head_step (Store (Val $ LitV $ LitLoc l) (Val $ w)) σ
              []
              (Val $ w) (state_upd_heap <[l := w]> σ)
              []
.

(** Properties for language interface *)

Global Instance fill_item_inj Ki : Inj (=) (=) (fill_item Ki).
Proof. destruct Ki; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki; simplify_option_eq; eauto. Qed.

Lemma val_head_stuck e1 σ1 κ e2 σ2 efs : head_step e1 σ1 κ e2 σ2 efs → to_val e1 = None.
Proof. destruct 1; naive_solver. Qed.

Lemma head_ctx_step_val Ki e σ1 κ e2 σ2 efs :
  head_step (fill_item Ki e) σ1 κ e2 σ2 efs → is_Some (to_val e).
Proof. destruct Ki; inversion_clear 1; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  fill_item Ki1 e1 = fill_item Ki2 e2 → Ki1 = Ki2.
Proof. destruct Ki1, Ki2; naive_solver eauto with f_equal. Qed.

Lemma tutorial_lang_mixin : EctxiLanguageMixin of_val to_val fill_item head_step.
Proof.
  split; apply _ || eauto using to_of_val, of_to_val, val_head_stuck,
    fill_item_val, fill_item_no_val_inj, head_ctx_step_val.
Qed.

(** Language *)
Canonical Structure tutorial_ectxi_lang := EctxiLanguage tutorial_lang_mixin.
Canonical Structure tutorial_ectx_lang := EctxLanguageOfEctxi tutorial_ectxi_lang.
Canonical Structure tutorial_lang := LanguageOfEctx tutorial_ectx_lang.

(** additional lemmas *)
Global Program Instance loc_infinite: Infinite loc :=
  inj_infinite (Loc) (λ x, Some (loc_val x)) (λ _, eq_refl).

Lemma alloc_fresh σ :
  let l := fresh (dom σ.(heap)) in
  head_step (Alloc) σ [] (Val $ LitV $ LitLoc l) (state_upd_heap <[l := LitV (LitInt 0)]> σ) [].
Proof. intros. apply AllocS. apply (not_elem_of_dom (D := gset loc)). apply is_fresh. Qed.
