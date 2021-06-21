From iris.program_logic Require Export language ectx_language ectxi_language.
From stdpp Require Export strings.
From stdpp Require Import gmap list.
From refinedc.lang Require Export base byte layout int_type loc val heap.
Set Default Proof Using "Type".
Open Scope Z_scope.

(** * Definition of the language *)

Definition label := string.
Definition var_name := string.

Inductive op_type : Set :=
| IntOp (i : int_type) | PtrOp.

(* see http://compcert.inria.fr/doc/html/compcert.cfrontend.Cop.html#binary_operation *)
Inductive bin_op : Set :=
| AddOp | SubOp | MulOp | DivOp | ModOp | AndOp | OrOp | XorOp | ShlOp
| ShrOp | EqOp | NeOp | LtOp | GtOp | LeOp | GeOp | Comma
(* Ptr is the second argument and pffset the first *)
| PtrOffsetOp (ly : layout) | PtrNegOffsetOp (ly : layout).

Inductive un_op : Set :=
| NotBoolOp | NotIntOp | NegOp | CastOp (ot : op_type).
Inductive order : Set :=
| ScOrd | Na1Ord | Na2Ord.

Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| CopyAllocId (ot1 : op_type) (e1 : expr) (e2 : expr)
| Deref (o : order) (ly : layout) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| Call (f : expr) (args : list expr)
| Concat (es : list expr)
| IfE (ot : op_type) (e1 e2 e3 : expr)
| SkipE (e : expr)
| StuckE (* stuck expression *)
.
End expr.
Arguments Call _%E _%E.
Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (ot1 : op_type) (e1 e2 : expr), P e1 → P e2 → P (CopyAllocId ot1 e1 e2)) →
  (∀ (o : order) (ly : layout) (e : expr), P e → P (Deref o ly e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (f : expr) (args : list expr), P f → Forall P args → P (Call f args)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (IfE ot e1 e2 e3)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hcall Hconcat *.
  8: { apply Hcall; [ |apply Forall_true => ?]; by apply: FIX. }
  8: { apply Hconcat. apply Forall_true => ?. by apply: FIX. }
  all: auto.
Qed.

Global Instance val_inj : Inj (=) (=) Val.
Proof. by move => ?? [->]. Qed.

(** Note that there is no explicit Fork. Instead the initial state can
contain multiple threads (like a processor which has a fixed number of
hardware threads). *)
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
(* m: map from values of e to indices into bs, def: default *)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ly : layout) (e1 e2 : expr) (s : stmt)
| SkipS (s : stmt)
| StuckS (* stuck statement *)
| ExprS (e : expr) (s : stmt)
.

Arguments Switch _%E _%E _%E.

Record function := {
  f_args : list (var_name * layout);
  f_local_vars : list (var_name * layout);
  (* TODO should we add this: f_ret : layout; ?*)
  f_code : gmap label stmt;
  f_init : label;
}.

(* TODO: put both function and bytes in the same heap or make pointers disjoint *)
Record state := {
  st_heap: heap_state;
  st_fntbl: gmap addr function;
}.

Definition heap_fmap (f : heap → heap) (σ : state) := {|
  st_heap := {| hs_heap := f σ.(st_heap).(hs_heap); hs_allocs := σ.(st_heap).(hs_allocs) |};
  st_fntbl := σ.(st_fntbl);
|}.

Record runtime_function := {
  (* locations of args and local vars are substitued in the body *)
  rf_fn : function;
  (* locations in the stack frame (locations of arguments and local
  vars allocated on Call, need to be freed by Return) *)
  rf_locs: list (loc * layout);
}.

Inductive runtime_expr :=
| Expr (e : rtexpr)
| Stmt (rf : runtime_function) (s : rtstmt)
| AllocFailed
with rtexpr :=
| RTVar (x : var_name)
| RTVal (v : val)
| RTUnOp (op : un_op) (ot : op_type) (e : runtime_expr)
| RTBinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : runtime_expr)
| RTCopyAllocId (ot1 : op_type) (e1 : runtime_expr) (e2 : runtime_expr)
| RTDeref (o : order) (ly : layout) (e : runtime_expr)
| RTCall (f : runtime_expr) (args : list runtime_expr)
| RTCAS (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTConcat (es : list runtime_expr)
| RTIfE (ot : op_type) (e1 e2 e3 : runtime_expr)
| RTSkipE (e : runtime_expr)
| RTStuckE
with rtstmt :=
| RTGoto (b : label)
| RTReturn (e : runtime_expr)
| RTSwitch (it : int_type) (e : runtime_expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| RTAssign (o : order) (ly : layout) (e1 e2 : runtime_expr) (s : stmt)
| RTSkipS (s : stmt)
| RTStuckS
| RTExprS (e : runtime_expr) (s : stmt)
.

Fixpoint to_rtexpr (e : expr) : runtime_expr :=
  Expr $ match e with
  | Var x => RTVar x
  | Val v => RTVal v
  | UnOp op ot e => RTUnOp op ot (to_rtexpr e)
  | BinOp op ot1 ot2 e1 e2 => RTBinOp op ot1 ot2 (to_rtexpr e1) (to_rtexpr e2)
  | CopyAllocId ot1 e1 e2 => RTCopyAllocId ot1 (to_rtexpr e1) (to_rtexpr e2)
  | Deref o ly e => RTDeref o ly (to_rtexpr e)
  | Call f args => RTCall (to_rtexpr f) (to_rtexpr <$> args)
  | CAS ot e1 e2 e3 => RTCAS ot (to_rtexpr e1) (to_rtexpr e2) (to_rtexpr e3)
  | Concat es => RTConcat (to_rtexpr <$> es)
  | IfE ot e1 e2 e3 => RTIfE ot (to_rtexpr e1) (to_rtexpr e2) (to_rtexpr e3)
  | SkipE e => RTSkipE (to_rtexpr e)
  | StuckE => RTStuckE
  end.
Definition coerce_rtexpr := to_rtexpr.
Coercion coerce_rtexpr : expr >-> runtime_expr.
Arguments coerce_rtexpr : simpl never.
Definition to_rtstmt (rf : runtime_function) (s : stmt) : runtime_expr :=
  Stmt rf $ match s with
  | Goto b => RTGoto b
  | Return e => RTReturn (to_rtexpr e)
  | Switch it e m bs def => RTSwitch it (to_rtexpr e) m bs def
  | Assign o ly e1 e2 s => RTAssign o ly (to_rtexpr e1) (to_rtexpr e2) s
  | SkipS s => RTSkipS s
  | StuckS => RTStuckS
  | ExprS e s => RTExprS (to_rtexpr e) s
  end.

Global Instance to_rtexpr_inj : Inj (=) (=) to_rtexpr.
Proof.
  elim => [ ^ e1 ] [ ^ e2 ] // ?; simplify_eq => //; try naive_solver.
  - f_equal. naive_solver.
    generalize dependent e2args.
    revert select (Forall _ _). elim. by case.
    move => ????? [|??]//. naive_solver.
  - generalize dependent e2es.
    revert select (Forall _ _). elim. by case.
    move => ????? [|??]//. naive_solver.
Qed.
Global Instance to_rtstmt_inj : Inj2 (=) (=) (=) to_rtstmt.
Proof. move => ? s1 ? s2 [-> ]. elim: s1 s2 => [ ^ e1 ] [ ^ e2 ] // ?; simplify_eq => //. Qed.

Implicit Type (l : loc) (re : rtexpr) (v : val) (h : heap) (σ : state) (ly : layout) (rs : rtstmt) (s : stmt) (sgn : signed) (rf : runtime_function).

(*** Substitution *)
Fixpoint subst (x : var_name) (v : val) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (x = y) then Val v else Var y
  | Val v => Val v
  | UnOp op ot e => UnOp op ot (subst x v e)
  | BinOp op ot1 ot2 e1 e2 => BinOp op ot1 ot2 (subst x v e1) (subst x v e2)
  | CopyAllocId ot1 e1 e2 => CopyAllocId ot1 (subst x v e1) (subst x v e2)
  | Deref o l e => Deref o l (subst x v e)
  | Call e es => Call (subst x v e) (subst x v <$> es)
  | CAS ly e1 e2 e3 => CAS ly (subst x v e1) (subst x v e2) (subst x v e3)
  | Concat el => Concat (subst x v <$> el)
  | IfE ot e1 e2 e3 => IfE ot (subst x v e1) (subst x v e2) (subst x v e3)
  | SkipE e => SkipE (subst x v e)
  | StuckE => StuckE
  end.

Fixpoint subst_l (xs : list (var_name * val)) (e : expr)  : expr :=
  match xs with
  | (x, v)::xs' => subst_l xs' (subst x v e)
  | _ => e
  end.

Fixpoint subst_stmt (xs : list (var_name * val)) (s : stmt) : stmt :=
  match s with
  | Goto b => Goto b
  | Return e => Return (subst_l xs e)
  | Switch it e m' bs def => Switch it (subst_l xs e) m' (subst_stmt xs <$> bs) (subst_stmt xs def)
  | Assign o ly e1 e2 s => Assign o ly (subst_l xs e1) (subst_l xs e2) (subst_stmt xs s)
  | SkipS s => SkipS (subst_stmt xs s)
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_l xs e) (subst_stmt xs s)
  end.

Definition subst_function (xs : list (var_name * val)) (f : function) : function := {|
  f_code := (subst_stmt xs) <$> f.(f_code);
  f_args := f.(f_args); f_init := f.(f_init); f_local_vars := f.(f_local_vars);
|}.

(*** Evaluation of operations *)

(* evaluation can be non-deterministic for comparing pointers *)
Inductive eval_bin_op : bin_op → op_type → op_type → state → val → val → val → Prop :=
| PtrOffsetOpIP v1 v2 σ o l ly it:
    val_to_Z_weak v1 it = Some o →
    val_to_loc v2 = Some l →
    (* TODO: should we have an alignment check here? *)
    heap_state_loc_in_bounds (l offset{ly}ₗ o) 0 σ.(st_heap) →
    eval_bin_op (PtrOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ o))
| PtrNegOffsetOpIP v1 v2 σ o l ly it:
    val_to_Z_weak v1 it = Some o →
    val_to_loc v2 = Some l →
    heap_state_loc_in_bounds (l offset{ly}ₗ -o) 0 σ.(st_heap) →
    (* TODO: should we have an alignment check here? *)
    eval_bin_op (PtrNegOffsetOp ly) (IntOp it) PtrOp σ v1 v2 (val_of_loc (l offset{ly}ₗ -o))
| EqOpPNull v1 v2 σ l v:
    heap_state_loc_in_bounds l 0%nat σ.(st_heap) →
    val_to_loc v1 = Some l →
    v2 = NULL →
    (* TODO ( see below ): Should we really hard code i32 here because of C? *)
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp σ v1 v2 v
| NeOpPNull v1 v2 σ l v:
    heap_state_loc_in_bounds l 0%nat σ.(st_heap) →
    val_to_loc v1 = Some l →
    v2 = NULL →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp σ v1 v2 v
| EqOpNullNull v1 v2 σ v:
    v1 = NULL →
    v2 = NULL →
    i2v (Z_of_bool true) i32 = v →
    eval_bin_op EqOp PtrOp PtrOp σ v1 v2 v
| NeOpNullNull v1 v2 σ v:
    v1 = NULL →
    v2 = NULL →
    i2v (Z_of_bool false) i32 = v →
    eval_bin_op NeOp PtrOp PtrOp σ v1 v2 v
| RelOpPP v1 v2 σ l1 l2 v b op:
    val_to_loc v1 = Some l1 →
    val_to_loc v2 = Some l2 →
    valid_ptr l1 σ.(st_heap) → valid_ptr l2 σ.(st_heap) →
    match op with
    | EqOp => Some (bool_decide (l1.2 = l2.2))
    | NeOp => Some (bool_decide (l1.2 ≠ l2.2))
    | LtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 < l2.2)) else None
    | GtOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 > l2.2)) else None
    | LeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 <= l2.2)) else None
    | GeOp => if bool_decide (l1.1 = l2.1) then Some (bool_decide (l1.2 >= l2.2)) else None
    | _ => None
    end = Some b →
    i2v (Z_of_bool b) i32 = v →
    eval_bin_op op PtrOp PtrOp σ v1 v2 v
| RelOpII op v1 v2 σ n1 n2 it b:
    match op with
    | EqOp => Some (bool_decide (n1 = n2))
    | NeOp => Some (bool_decide (n1 ≠ n2))
    | LtOp => Some (bool_decide (n1 < n2))
    | GtOp => Some (bool_decide (n1 > n2))
    | LeOp => Some (bool_decide (n1 <= n2))
    | GeOp => Some (bool_decide (n1 >= n2))
    | _ => None
    end = Some b →
    val_to_Z_weak v1 it = Some n1 →
    val_to_Z_weak v2 it = Some n2 →
    (* TODO: What is the right int type of the result here? C seems to
    use i32 but maybe we don't want to hard code that. *)
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 (i2v (Z_of_bool b) i32)
| ArithOpII op v1 v2 σ n1 n2 it n v:
    match op with
    | AddOp => Some (n1 + n2)
    | SubOp => Some (n1 - n2)
    | MulOp => Some (n1 * n2)
    (* we need to take `quot` and `rem` here for the correct rounding
    behavior, i.e. rounding towards 0 (instead of `div` and `mod`,
    which round towards floor)*)
    | DivOp => if bool_decide (n2 ≠ 0) then Some (n1 `quot` n2) else None
    | ModOp => if bool_decide (n2 ≠ 0) then Some (n1 `rem` n2) else None
    | AndOp => Some (Z.land n1 n2)
    | OrOp => Some (Z.lor n1 n2)
    | XorOp => Some (Z.lxor n1 n2)
    (* For shift operators (`ShlOp` and `ShrOp`), behaviors are defined if:
       - lhs is nonnegative, and
       - rhs (also nonnegative) is less than the number of bits in lhs.
       See: https://en.cppreference.com/w/c/language/operator_arithmetic, "Shift operators". *)
    | ShlOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≪ n2) else None
    (* NOTE: when lhs is negative, Coq's `≫` is not semantically equivalent to C's `>>`.
       Counterexample: Coq `-1000 ≫ 10 = 0`; C `-1000 >> 10 == -1`.
       This is because `≫` is implemented by `Z.div`. *)
    | ShrOp => if bool_decide (0 ≤ n1 ∧ 0 ≤ n2 < bits_per_int it) then Some (n1 ≫ n2) else None
    | _ => None
    end = Some n →
    val_to_Z_weak v1 it = Some n1 →
    val_to_Z_weak v2 it = Some n2 →
    val_of_Z (if it_signed it then n else n `mod` int_modulus it) it = Some v →
    eval_bin_op op (IntOp it) (IntOp it) σ v1 v2 v
| CommaOp ot1 ot2 σ v1 v2:
    eval_bin_op Comma ot1 ot2 σ v1 v2 v2
.

Inductive eval_un_op : un_op → op_type → state → val → val → Prop :=
| CastOpII itt its σ vs vt i:
    val_to_int_repr vs its = Some i →
    val_of_int_repr i itt = Some vt →
    eval_un_op (CastOp (IntOp itt)) (IntOp its) σ vs vt
| CastOpPP σ vs vt l:
    val_to_loc vs = Some l →
    val_of_loc l = vt →
    eval_un_op (CastOp PtrOp) PtrOp σ vs vt
| CastOpPI it σ vs vt l:
    val_to_loc vs = Some l →
    val_of_int_repr (IRLoc l) it = Some vt →
    block_alive l σ.(st_heap) →
    eval_un_op (CastOp (IntOp it)) PtrOp σ vs vt
| CastOpPINull it σ vs vt:
    vs = NULL →
    val_of_Z 0 it = Some vt →
    eval_un_op (CastOp (IntOp it)) PtrOp σ vs vt
| CastOpIP it σ vs vt l l':
    val_to_loc_weak vs it = Some l →
    val_of_loc l' = vt →
    (** This is using that the address 0 is never alive. *)
    l' = (if bool_decide (block_alive l σ.(st_heap)) then l else
           (if bool_decide (l.2 = 0) then NULL_loc else (ProvAlloc None, l.2))) →
    eval_un_op (CastOp PtrOp) (IntOp it) σ vs vt
| NegOpI it σ vs vt n:
    val_to_Z_weak vs it = Some n →
    val_of_Z (-n) it = Some vt →
    eval_un_op NegOp (IntOp it) σ vs vt
| NotIntOpI it σ vs vt n:
    val_to_Z_weak vs it = Some n →
    val_of_Z (if it_signed it then Z.lnot n else Z_lunot (bits_per_int it) n) it = Some vt →
    eval_un_op NotIntOp (IntOp it) σ vs vt
.

(*** Evaluation of Expressions *)

Inductive expr_step : expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| SkipES v σ:
    expr_step (SkipE (Val v)) σ [] (Val v) σ []
| UnOpS op v σ v' ot:
    eval_un_op op ot σ v v' →
    expr_step (UnOp op ot (Val v)) σ [] (Val v') σ []
| BinOpS op v1 v2 σ v' ot1 ot2:
    eval_bin_op op ot1 ot2 σ v1 v2 v' →
    expr_step (BinOp op ot1 ot2 (Val v1) (Val v2)) σ [] (Val v') σ []
| DerefS o v l ly v' σ:
    let start_st st := ∃ n, st = if o is Na2Ord then RSt (S n) else RSt n in
    let end_st st :=
      match o, st with
      | Na1Ord, Some (RSt n)     => RSt (S n)
      | Na2Ord, Some (RSt (S n)) => RSt n
      | ScOrd , Some st          => st
      |  _    , _                => WSt (* unreachable *)
      end
    in
    let end_expr := if o is Na1Ord then Deref Na2Ord ly (Val v) else Val v' in
    val_to_loc v = Some l →
    heap_at l ly v' start_st σ.(st_heap).(hs_heap) →
    expr_step (Deref o ly (Val v)) σ [] end_expr (heap_fmap (heap_upd l v' end_st) σ) []
(* TODO: look at CAS and see whether it makes sense. Also allow
comparing pointers? (see lambda rust) *)
(* corresponds to atomic_compare_exchange_strong, see https://en.cppreference.com/w/c/atomic/atomic_compare_exchange *)
| CasFailS l1 l2 vo ve σ z1 z2 v1 v2 v3 it:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_Z_weak vo it = Some z1 →
    val_to_Z_weak ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool false)) (heap_fmap (heap_upd l2 vo (λ _, RSt 0%nat)) σ) []
| CasSucS l1 l2 it vo ve σ z1 z2 v1 v2 v3:
    val_to_loc v1 = Some l1 →
    heap_at l1 (it_layout it) vo (λ st, st = RSt 0%nat) σ.(st_heap).(hs_heap) →
    val_to_loc v2 = Some l2 →
    heap_at l2 (it_layout it) ve (λ st, ∃ n, st = RSt n) σ.(st_heap).(hs_heap) →
    val_to_Z_weak vo it = Some z1 →
    val_to_Z_weak ve it = Some z2 →
    v3 `has_layout_val` it_layout it →
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 = z2 →
    expr_step (CAS (IntOp it) (Val v1) (Val v2) (Val v3)) σ []
              (Val (val_of_bool true)) (heap_fmap (heap_upd l1 v3 (λ _, RSt 0%nat)) σ) []
| CallS lsa lsv σ hs' hs'' vf vs f rf fn fn' a:
    val_to_loc vf = Some f →
    f = fn_loc a →
    σ.(st_fntbl) !! a = Some fn →
    length lsa = length fn.(f_args) →
    length lsv = length fn.(f_local_vars) →
    (* substitute the variables in fn with the corresponding locations *)
    fn' = subst_function (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1) (val_of_loc <$> (lsa ++ lsv))) fn →
    (* check the layout of the arguments *)
    Forall2 has_layout_val vs fn.(f_args).*2 →
    (* ensure that locations are aligned *)
    Forall2 has_layout_loc lsa fn.(f_args).*2 →
    Forall2 has_layout_loc lsv fn.(f_local_vars).*2 →
    (* initialize the local vars to poison *)
    alloc_new_blocks σ.(st_heap) lsv ((λ p, replicate p.2.(ly_size) MPoison) <$> fn.(f_local_vars)) hs' →
    (* initialize the arguments with the supplied values *)
    alloc_new_blocks hs' lsa vs hs'' →
    (* add used blocks allocations  *)
    rf = {| rf_fn := fn'; rf_locs := zip lsa fn.(f_args).*2 ++ zip lsv fn.(f_local_vars).*2; |} →
    expr_step (Call (Val vf) (Val <$> vs)) σ [] (to_rtstmt rf (Goto fn'.(f_init))) {| st_heap := hs''; st_fntbl := σ.(st_fntbl)|} []
| CallFailS σ vf vs f fn a:
    val_to_loc vf = Some f →
    f = fn_loc a →
    σ.(st_fntbl) !! a = Some fn →
    Forall2 has_layout_val vs fn.(f_args).*2 →
    expr_step (Call (Val vf) (Val <$> vs)) σ [] AllocFailed σ []
| ConcatS vs σ:
    expr_step (Concat (Val <$> vs)) σ [] (Val (mjoin vs)) σ []
| CopyAllocIdS σ v1 v2 a it l:
    val_to_Z_weak v1 it = Some a →
    val_to_loc v2 = Some l →
    valid_ptr (l.1, a) σ.(st_heap) →
    expr_step (CopyAllocId (IntOp it) (Val v1) (Val v2)) σ [] (Val (val_of_loc (l.1, a))) σ []
| IfES v it e1 e2 n σ:
    val_to_Z_weak v it = Some n →
    expr_step (IfE (IntOp it) (Val v) e1 e2) σ [] (if bool_decide (n ≠ 0) then e1 else e2)  σ []
(* no rule for StuckE *)
.

(*** Evaluation of statements *)
Inductive stmt_step : stmt → runtime_function → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| AssignS (o : order) rf σ s v1 v2 l v' ly:
    let start_st st := st = if o is Na2Ord then WSt else RSt 0%nat in
    let end_st _ := if o is Na1Ord then WSt else RSt 0%nat in
    let end_val  := if o is Na1Ord then v' else v2 in
    let end_stmt := if o is Na1Ord then Assign Na2Ord ly (Val v1) (Val v2) s else s in
    val_to_loc v1 = Some l →
    v2 `has_layout_val` ly →
    heap_at l ly v' start_st σ.(st_heap).(hs_heap) →
    stmt_step (Assign o ly (Val v1) (Val v2) s) rf σ [] (to_rtstmt rf end_stmt) (heap_fmap (heap_upd l end_val end_st) σ) []
| SwitchS rf σ v n m bs s def it :
    val_to_Z_weak v it = Some n →
    (∀ i : nat, m !! n = Some i → is_Some (bs !! i)) →
    stmt_step (Switch it (Val v) m bs def) rf σ [] (to_rtstmt rf (default def (i ← m !! n; bs !! i))) σ []
| GotoS rf σ b s :
    rf.(rf_fn).(f_code) !! b = Some s →
    stmt_step (Goto b) rf σ [] (to_rtstmt rf s) σ []
| ReturnS rf σ hs v:
    free_blocks σ.(st_heap) rf.(rf_locs) hs → (* Deallocate the stack. *)
    stmt_step (Return (Val v)) rf σ [] (Val v) {| st_fntbl := σ.(st_fntbl); st_heap := hs |} []
| SkipSS rf σ s :
    stmt_step (SkipS s) rf σ [] (to_rtstmt rf s) σ []
| ExprSS rf σ s v:
    stmt_step (ExprS (Val v) s) rf σ [] (to_rtstmt rf s) σ []
(* no rule for StuckS *)
.

(*** Evaluation of runtime_expr *)
Inductive runtime_step : runtime_expr → state → list Empty_set → runtime_expr → state → list runtime_expr → Prop :=
| ExprStep e σ κs e' σ' efs:
    expr_step e σ κs e' σ' efs →
    runtime_step (to_rtexpr e) σ κs e' σ' efs
| StmtStep s rf σ κs e' σ' efs:
    stmt_step s rf σ κs e' σ' efs →
    runtime_step (to_rtstmt rf s) σ κs e' σ' efs
| AllocFailedStep σ :
    (* Alloc failure is nb, not ub so we go into an infinite loop*)
    runtime_step AllocFailed σ [] AllocFailed σ [].

Lemma expr_step_preserves_invariant e1 e2 σ1 σ2 κs efs:
  expr_step e1 σ1 κs e2 σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] // *.
  all: repeat select (heap_at _ _ _ _ _) ltac:(fun H => destruct H as [?[?[??]]]).
  all: try (rewrite /heap_fmap/=; eapply heap_update_heap_state_invariant => //).
  all: try (unfold has_layout_val in *; by etransitivity).
  repeat eapply alloc_new_blocks_invariant => //.
Qed.

Lemma stmt_step_preserves_invariant s rf e σ1 σ2 κs efs:
  stmt_step s rf σ1 κs e σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] //; clear.
  - move => o *.
    revert select (heap_at _ _ _ _ _) => -[?[?[??]]].
    rewrite /heap_fmap/=. eapply heap_update_heap_state_invariant => //.
    match goal with H : _ `has_layout_val` _ |- _ => rewrite H end.
    by destruct o.
  - move => ??? _ Hfree Hinv. by eapply free_blocks_invariant.
Qed.

Lemma runtime_step_preserves_invariant e1 e2 σ1 σ2 κs efs:
  runtime_step e1 σ1 κs e2 σ2 efs →
  heap_state_invariant σ1.(st_heap) →
  heap_state_invariant σ2.(st_heap).
Proof.
  move => [] // *.
  - by eapply expr_step_preserves_invariant.
  - by eapply stmt_step_preserves_invariant.
Qed.

(*** evaluation contexts *)
(** for expressions*)
Inductive expr_ectx :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : runtime_expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| CopyAllocIdLCtx (ot1 : op_type) (e2 : runtime_expr)
| CopyAllocIdRCtx (ot1 : op_type) (v1 : val)
| DerefCtx (o : order) (l : layout)
| CallLCtx (args : list runtime_expr)
| CallRCtx (f : val) (vl : list val) (el : list runtime_expr)
| CASLCtx (ot : op_type) (e2 e3 : runtime_expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : runtime_expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| ConcatCtx (vs : list val) (es : list runtime_expr)
| IfECtx (ot : op_type) (e2 e3 : runtime_expr)
| SkipECtx
.

Definition expr_fill_item (Ki : expr_ectx) (e : runtime_expr) : rtexpr :=
  match Ki with
  | UnOpCtx op ot => RTUnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => RTBinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => RTBinOp op ot1 ot2 (Val v1) e
  | CopyAllocIdLCtx ot1 e2 => RTCopyAllocId ot1 e e2
  | CopyAllocIdRCtx ot1 v1 => RTCopyAllocId ot1 (Val v1) e
  | DerefCtx o l => RTDeref o l e
  | CallLCtx args => RTCall e args
  | CallRCtx f vl el => RTCall (Val f) ((Expr <$> (RTVal <$> vl)) ++ e :: el)
  | CASLCtx ot e2 e3 => RTCAS ot e e2 e3
  | CASMCtx ot v1 e3 => RTCAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => RTCAS ot (Val v1) (Val v2) e
  | ConcatCtx vs es => RTConcat ((Expr <$> (RTVal <$> vs)) ++ e :: es)
  | IfECtx ot e2 e3 => RTIfE ot e e2 e3
  | SkipECtx => RTSkipE e
  end.

(** Statements *)
Inductive stmt_ectx :=
(* Assignment is evalutated right to left, otherwise we need to split contexts *)
| AssignRCtx (o : order) (ly : layout) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ly : layout) (v2 : val) (s : stmt)
| ReturnCtx
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| ExprSCtx (s : stmt)
.

Definition stmt_fill_item (Ki : stmt_ectx) (e : runtime_expr) : rtstmt :=
  match Ki with
  | AssignRCtx o ly e1 s => RTAssign o ly e1 e s
  | AssignLCtx o ly v2 s => RTAssign o ly e (Val v2) s
  | ReturnCtx => RTReturn e
  | SwitchCtx it m bs def => RTSwitch it e m bs def
  | ExprSCtx s => RTExprS e s
  end.
Definition to_val (e : runtime_expr) : option val :=
  match e with
  | Expr (RTVal v) => Some v
  | _ => None
  end.

Definition of_val (v : val) : runtime_expr := Expr (RTVal v).

Inductive lang_ectx :=
| ExprCtx (E : expr_ectx)
| StmtCtx (E : stmt_ectx) (rf : runtime_function).

Definition lang_fill_item (Ki : lang_ectx) (e : runtime_expr) : runtime_expr :=
  match Ki with
  | ExprCtx E => Expr (expr_fill_item E e)
  | StmtCtx E rf => Stmt rf (stmt_fill_item E e)
  end.

Lemma list_expr_val_eq_inv vl1 vl2 e1 e2 el1 el2 :
  to_val e1 = None → to_val e2 = None →
  (Expr <$> (RTVal <$> vl1)) ++ e1 :: el1 = (Expr <$> (RTVal <$> vl2)) ++ e2 :: el2 →
  vl1 = vl2 ∧ e1 = e2 ∧ el1 = el2.
Proof.
  revert vl2; induction vl1; destruct vl2; intros H1 H2; inversion 1.
  - done.
  - subst. by inversion H1.
  - subst. by inversion H2.
  - destruct (IHvl1 vl2); auto. split; f_equal; auto.
Qed.

Lemma list_expr_val_eq_false vl1 vl2 e el :
  to_val e = None → to_rtexpr <$> (Val <$> vl1) = (Expr <$> (RTVal <$> vl2)) ++ e :: el → False.
Proof.
  move => He. elim: vl2 vl1 => [[]//=*|v vl2 IH [|??]?]; csimpl in *; simplify_eq; eauto.
Qed.

Lemma of_to_val (e : runtime_expr) v : to_val e = Some v → Expr (RTVal v) = e.
Proof. case: e => // -[]//. naive_solver. Qed.

Lemma val_stuck e1 σ1 κ e2 σ2 ef :
  runtime_step e1 σ1 κ e2 σ2 ef → to_val e1 = None.
Proof. destruct 1 => //. revert select (expr_step _ _ _ _ _ _). by destruct 1. Qed.

Instance fill_item_inj Ki : Inj (=) (=) (lang_fill_item Ki).
Proof. destruct Ki as [E|E ?]; destruct E; intros ???; simplify_eq/=; auto with f_equal. Qed.

Lemma fill_item_val Ki e :
  is_Some (to_val (lang_fill_item Ki e)) → is_Some (to_val e).
Proof. intros [v ?]. destruct Ki as [[]|[] ?]; simplify_option_eq; eauto. Qed.

Lemma fill_item_no_val_inj Ki1 Ki2 e1 e2 :
  to_val e1 = None → to_val e2 = None →
  lang_fill_item Ki1 e1 = lang_fill_item Ki2 e2 → Ki1 = Ki2.
Proof.
  move: Ki1 Ki2 => [ ^ Ki1] [ ^Ki2] He1 He2 ? //; simplify_eq; try done; f_equal.
  all: destruct Ki1E, Ki2E => //; simplify_eq => //.
  all: efeed pose proof list_expr_val_eq_inv as HEQ; [| | done |] => //; naive_solver.
Qed.

Lemma expr_ctx_step_val Ki e σ1 κ e2 σ2 ef :
  runtime_step (lang_fill_item Ki e) σ1 κ e2 σ2 ef → is_Some (to_val e).
Proof.
  destruct Ki as [[]|[]?]; inversion 1; simplify_eq.
  all: try (revert select (expr_step _ _ _ _ _ _)).
  all: try (revert select (stmt_step _ _ _ _ _ _ _)).
  all: inversion 1; simplify_eq/=; eauto.
  all: apply not_eq_None_Some; intros ?; by eapply list_expr_val_eq_false.
Qed.

Lemma c_lang_mixin : EctxiLanguageMixin of_val to_val lang_fill_item runtime_step.
Proof.
  split => //; eauto using of_to_val, val_stuck, fill_item_inj, fill_item_val, fill_item_no_val_inj, expr_ctx_step_val.
Qed.
Canonical Structure c_ectxi_lang := EctxiLanguage c_lang_mixin.
Canonical Structure c_ectx_lang := EctxLanguageOfEctxi c_ectxi_lang.
Canonical Structure c_lang := LanguageOfEctx c_ectx_lang.

(** * Useful instances and canonical structures *)

Instance mbyte_inhabited : Inhabited mbyte := populate (MPoison).
Instance val_inhabited : Inhabited val := _.
Instance expr_inhabited : Inhabited expr := populate (Val inhabitant).
Instance stmt_inhabited : Inhabited stmt := populate (Goto "a").
Instance function_inhabited : Inhabited function :=
  populate {| f_args := []; f_local_vars := []; f_code := ∅; f_init := "" |}.
Instance heap_state_inhabited : Inhabited heap_state :=
  populate {| hs_heap := inhabitant; hs_allocs := inhabitant; |}.
Instance state_inhabited : Inhabited state :=
  populate {| st_heap := inhabitant; st_fntbl := inhabitant; |}.

Canonical Structure mbyteO := leibnizO mbyte.
Canonical Structure functionO := leibnizO function.
Canonical Structure locO := leibnizO loc.
Canonical Structure alloc_idO := leibnizO alloc_id.
Canonical Structure layoutO := leibnizO layout.
Canonical Structure valO := leibnizO val.
Canonical Structure exprO := leibnizO expr.
Canonical Structure allocationO := leibnizO allocation.
