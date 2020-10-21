From stdpp Require Import fin_maps.
From refinedc.lang Require Export notation.
Set Default Proof Using "Type".

Module W.
(*** Expressions *)
Section expr.
Local Unset Elimination Schemes.
Inductive expr :=
| Var (x : var_name)
| Loc (l : loc)
| Val (v : val)
| UnOp (op : un_op) (ot : op_type) (e : expr)
| BinOp (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr)
| Deref (o : order) (ly : layout) (e : expr)
| CAS (ot : op_type) (e1 e2 e3 : expr)
| Concat (es : list expr)
| SkipE (e : expr)
| StuckE
(* new constructors *)
| Use (o : order) (ly : layout) (e : expr)
| AddrOf (e : expr)
| GetMember (e : expr) (s : struct_layout) (m : var_name)
| GetMemberUnion (e : expr) (ul : union_layout) (m : var_name)
| AnnotExpr (n : nat) {A} (a : A) (e : expr)
| LocInfoE (a : location_info) (e : expr)
| StructInit (ly : struct_layout) (fs : list (string * expr))
(* for opaque expressions*)
| Expr (e : lang.expr)
.
End expr.

Lemma expr_ind (P : expr → Prop) :
  (∀ (x : var_name), P (Var x)) →
  (∀ (l : loc), P (Loc l)) →
  (∀ (v : val), P (Val v)) →
  (∀ (op : un_op) (ot : op_type) (e : expr), P e → P (UnOp op ot e)) →
  (∀ (op : bin_op) (ot1 ot2 : op_type) (e1 e2 : expr), P e1 → P e2 → P (BinOp op ot1 ot2 e1 e2)) →
  (∀ (o : order) (ly : layout) (e : expr), P e → P (Deref o ly e)) →
  (∀ (ot : op_type) (e1 e2 e3 : expr), P e1 → P e2 → P e3 → P (CAS ot e1 e2 e3)) →
  (∀ (es : list expr), Forall P es → P (Concat es)) →
  (∀ (e : expr), P e → P (SkipE e)) →
  (P StuckE) →
  (∀ (o : order) (ly : layout) (e : expr), P e → P (Use o ly e)) →
  (∀ (e : expr), P e → P (AddrOf e)) →
  (∀ (e : expr) (s : struct_layout) (m : var_name), P e → P (GetMember e s m)) →
  (∀ (e : expr) (ul : union_layout) (m : var_name), P e → P (GetMemberUnion e ul m)) →
  (∀ (n : nat) (A : Type) (a : A) (e : expr), P e → P (AnnotExpr n a e)) →
  (∀ (a : location_info) (e : expr), P e → P (LocInfoE a e)) →
  (∀ (ly : struct_layout) (fs : list (string * expr)), Forall (λ se, P se) fs.*2 → P (StructInit ly fs)) →
  (∀ (e : lang.expr), P (Expr e)) → ∀ (e : expr), P e.
Proof.
  move => *. generalize dependent P => P. match goal with | e : expr |- _ => revert e end.
  fix FIX 1. move => [ ^e] => ??????? Hconcat ???????? Hstruct *.
  8: {
    apply Hconcat. apply Forall_true => ?. by apply: FIX.
  }
  16: {
    apply Hstruct. apply Forall_fmap. apply Forall_true => ?. by apply: FIX.
  }
  all: auto.
Qed.

Fixpoint to_expr (e : expr) : lang.expr :=
  match e with
  | Val v => v
  | Loc l => val_of_loc l
  | Var x => lang.Var x
  | UnOp op ot e  => lang.UnOp op ot (to_expr e)
  | BinOp op ot1 ot2 e1 e2 => lang.BinOp op ot1 ot2 (to_expr e1) (to_expr e2)
  | Deref o ly e => lang.Deref o ly (to_expr e)
  | CAS ot e1 e2 e3 => lang.CAS ot (to_expr e1) (to_expr e2) (to_expr e3)
  | Concat es => lang.Concat (to_expr <$> es)
  | SkipE e => lang.SkipE (to_expr e)
  | StuckE => lang.StuckE
  | Use o ly e => notation.Use o ly (to_expr e)
  | AddrOf e => notation.AddrOf (to_expr e)
  | AnnotExpr n a e => notation.AnnotExpr n a (to_expr e)
  | LocInfoE a e => notation.LocInfo a (to_expr e)
  | StructInit ly fs => notation.StructInit ly (prod_map id to_expr <$> fs)
  | GetMember e s m => notation.GetMember (to_expr e) s m
  | GetMemberUnion e ul m => notation.GetMemberUnion (to_expr e) ul m
  | Expr e => e
  end.

Ltac of_expr e :=
  lazymatch e with
  | [] => constr:(@nil expr)
  | ?e :: ?es =>
    let e := of_expr e in
    let es := of_expr es in
    constr:(e :: es)

  | lang.Val (lang.val_of_loc ?l) => constr:(Loc l)
  | notation.AddrOf ?e =>
    let e := of_expr e in constr:(AddrOf e)
  | notation.AnnotExpr ?n ?a ?e =>
    let e := of_expr e in constr:(AnnotExpr n a e)
  | notation.LocInfo ?a ?e =>
    let e := of_expr e in constr:(LocInfoE a e)
  | notation.StructInit ?ly ?fs =>
    let fs := of_field_expr fs in constr:(StructInit ly fs)
  | notation.GetMember ?e ?s ?m =>
    let e := of_expr e in constr:(GetMember e s m)
  | notation.GetMemberUnion ?e ?ul ?m =>
    let e := of_expr e in constr:(GetMemberUnion e ul m)
  | notation.Use ?o ?ly ?e =>
    let e := of_expr e in constr:(Use o ly e)
  | lang.Val ?x => constr:(Val x)
  | lang.Var ?x => constr:(Var x)
  | lang.UnOp ?op ?ot ?e =>
    let e := of_expr e in constr:(UnOp op ot e)
  | lang.BinOp ?op ?ot1 ?ot2 ?e1 ?e2 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in constr:(BinOp op ot1 ot2 e1 e2)
  | lang.Deref ?o ?ly ?e =>
    let e := of_expr e in constr:(Deref o ly e)
  | lang.CAS ?ot ?e1 ?e2 ?e3 =>
    let e1 := of_expr e1 in let e2 := of_expr e2 in let e3 := of_expr e3 in constr:(CAS ot e1 e2 e3)
  | lang.Concat ?es =>
    let es := of_expr es in constr:(Concat es)
  | lang.SkipE ?e =>
    let e := of_expr e in constr:(SkipE e)
  | lang.StuckE => constr:(StuckE e)
  | _ => constr:(Expr e)
  end
with of_field_expr fs :=
  lazymatch fs with
  | [] => constr:(@nil (string * expr))
  | (?id, ?e) :: ?fs =>
    let e := of_expr e in
    let fs := of_field_expr fs in
    constr:((id, e) :: fs)
  end.

Inductive ectx_item :=
| UnOpCtx (op : un_op) (ot : op_type)
| BinOpLCtx (op : bin_op) (ot1 ot2 : op_type) (e2 : expr)
| BinOpRCtx (op : bin_op) (ot1 ot2 : op_type) (v1 : val)
| DerefCtx (o : order) (l : layout)
| CASLCtx (ot : op_type) (e2 e3 : expr)
| CASMCtx (ot : op_type) (v1 : val) (e3 : expr)
| CASRCtx (ot : op_type) (v1 v2 : val)
| ConcatCtx (vs : list val) (es : list expr)
| SkipECtx
(* new constructors *)
| UseCtx (o : order) (ly : layout)
| AddrOfCtx
| AnnotExprCtx (n : nat) {A} (a : A)
| LocInfoECtx (a : location_info)
(* the following would not work, thus we don't have a context, but prove a specialized bind rule*)
(*| StructInitCtx (ly : struct_layout) (vfs : list (string * val)) (id : string) (efs : list (string * expr))*)
| GetMemberCtx (s : struct_layout) (m : var_name)
| GetMemberUnionCtx (ul : union_layout) (m : var_name)
.

Definition fill_item (Ki : ectx_item) (e : expr) : expr :=
  match Ki with
  | UnOpCtx op ot => UnOp op ot e
  | BinOpLCtx op ot1 ot2 e2 => BinOp op ot1 ot2 e e2
  | BinOpRCtx op ot1 ot2 v1 => BinOp op ot1 ot2 (Val v1) e
  | DerefCtx o l => Deref o l e
  | CASLCtx ot e2 e3 => CAS ot e e2 e3
  | CASMCtx ot v1 e3 => CAS ot (Val v1) e e3
  | CASRCtx ot v1 v2 => CAS ot (Val v1) (Val v2) e
  | ConcatCtx vs es => Concat ((Val <$> vs) ++ e :: es)
  | SkipECtx => SkipE e
  | UseCtx o l => Use o l e
  | AddrOfCtx => AddrOf e
  | AnnotExprCtx n a => AnnotExpr n a e
  | LocInfoECtx a => LocInfoE a e
  | GetMemberCtx s m => GetMember e s m
  | GetMemberUnionCtx ul m => GetMemberUnion e ul m
  end.

Definition fill (K : list ectx_item) (e : expr) : expr := foldl (flip fill_item) e K.
Lemma fill_app (K1 K2 : list ectx_item) e : fill (K1 ++ K2) e = fill K2 (fill K1 e).
Proof. apply foldl_app. Qed.

Fixpoint find_expr_fill (e : expr) (bind_val : bool) : option (list ectx_item * expr) :=
  match e with
  | Var _ => None
  | Val v => if bind_val then Some ([], Val v) else None
  | Loc l => if bind_val then Some ([], Loc l) else None
  | Expr e => Some ([], Expr e)
  | StuckE => Some ([], StuckE)
  | UnOp op ot e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [UnOpCtx op ot], e') else Some ([], e)
  | BinOp op ot1 ot2 e1 e2 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [BinOpLCtx op ot1 ot2 e2], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
           if e1 is Val v then Some (Ks ++ [BinOpRCtx op ot1 ot2 v], e') else None
         else Some ([], e)
  | CAS ot e1 e2 e3 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [CASLCtx ot e2 e3], e')
    else if find_expr_fill e2 bind_val is Some (Ks, e') then
      if e1 is Val v1 then Some (Ks ++ [CASMCtx ot v1 e3], e') else None
    else if find_expr_fill e3 bind_val is Some (Ks, e') then
      if e1 is Val v1 then if e2 is Val v2 then Some (Ks ++ [CASRCtx ot v1 v2], e') else None else None
    else Some ([], e)
  | Concat _ => None
  | SkipE e1 =>
    if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [SkipECtx], e') else Some ([], e)
  | Deref o ly e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [DerefCtx o ly], e') else Some ([], e)
  | Use o ly e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [UseCtx o ly], e') else Some ([], e)
  | AddrOf e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AddrOfCtx], e') else Some ([], e)
  | AnnotExpr n a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [AnnotExprCtx n a], e') else Some ([], e)
  | LocInfoE a e1 => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [LocInfoECtx a], e') else Some ([], e)
  | StructInit _ _ => None
  | GetMember e1 s m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberCtx s m], e') else Some ([], e)
  | GetMemberUnion e1 ul m => if find_expr_fill e1 bind_val is Some (Ks, e') then
      Some (Ks ++ [GetMemberUnionCtx ul m], e') else Some ([], e)
  end.

Lemma find_expr_fill_correct b e Ks e':
  find_expr_fill e b = Some (Ks, e') → e = fill Ks e'.
Proof.
  elim: e Ks e' => //= *;
     repeat (try case_match; simpl in *; simplify_eq => /=);
     rewrite ?fill_app /=; f_equal; eauto.
Qed.

Lemma ectx_item_correct Ks:
  ∃ Ks', ∀ e, to_expr (fill Ks e) = ectxi_language.fill Ks' (to_expr e).
Proof.
  elim/rev_ind: Ks. by exists [].
  move => K Ks [Ks' IH].
  move: K => [|||||||||||n|||] *; [
    eexists (_ ++ [lang.UnOpCtx _ _])|
    eexists (_ ++ [lang.BinOpLCtx _ _ _ _])|
    eexists (_ ++ [lang.BinOpRCtx _ _ _ _])|
    eexists (_ ++ [lang.DerefCtx _ _])|
    eexists (_ ++ [lang.CASLCtx _ _ _])|
    eexists (_ ++ [lang.CASMCtx _ _ _])|
    eexists (_ ++ [lang.CASRCtx _ _ _])|
    eexists (_ ++ [lang.ConcatCtx _ _])|
    eexists (_ ++ [lang.SkipECtx])|
    eexists (_ ++ [lang.DerefCtx _ _])|
    eexists (_)|
    eexists (_ ++ replicate n lang.SkipECtx )|
    eexists (_)|
    eexists (_ ++ [lang.BinOpLCtx _ _ _ _])|
    eexists (_)|
    ..] => ?; rewrite fill_app ?ectxi_language.fill_app /= /notation.GetMember; f_equal; eauto.
  - (** Concat *)
    rewrite fmap_app fmap_cons. repeat f_equal; eauto.
    rewrite -list_fmap_compose. by apply: list_fmap_ext.
  - (** AnnotExpr *)
    elim: n. by simpl; eauto.
    move => n. by rewrite /notation.AnnotExpr replicate_S_end ectxi_language.fill_app /= => ->.
Qed.

Lemma to_expr_val_list (vl : list val) :
  to_expr <$> (Val <$> vl) = lang.Val <$> vl.
Proof. elim: vl => //; csimpl => *. by f_equal. Qed.

(*** Statements *)

Section stmt.
Local Unset Elimination Schemes.
Inductive stmt :=
| Goto (b : label)
| Return (e : expr)
| Switch (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt)
| Assign (o : order) (ly : layout) (e1 e2 : expr) (s : stmt)
| Call (ret : var_name) (f : expr) (args : list expr) (s : stmt)
| SkipS (s : stmt)
| StuckS
| ExprS (e : expr) (s : stmt)

| If (e : expr) (s1 s2 : stmt)
| Assert (e : expr) (s : stmt)
| AnnotStmt (n : nat) {A} (a : A) (s : stmt)
| LocInfoS (a : location_info) (s : stmt)
(* for opaque statements *)
| Stmt (s : lang.stmt).
End stmt.

Lemma stmt_ind (P : stmt → Prop):
  (∀ b : label, P (Goto b)) →
  (∀ e : expr, P (Return e)) →
  (∀ (it : int_type) (e : expr) (m : gmap Z nat) (bs : list stmt) (def : stmt), P def → Forall P bs → P (Switch it e m bs def)) →
  (∀ (o : order) (ly : layout) (e1 e2 : expr) (s : stmt), P s → P (Assign o ly e1 e2 s)) →
  (∀ (ret : var_name) (f3 : expr) (args : list expr) (s : stmt), P s → P (Call ret f3 args s)) →
  (∀ s : stmt, P s → P (SkipS s)) →
  (P StuckS) →
  (∀ (e : expr) (s : stmt), P s → P (ExprS e s)) →
  (∀ (e : expr) (s1 : stmt), P s1 → ∀ s2 : stmt, P s2 → P (If e s1 s2)) →
  (∀ (e : expr) (s : stmt), P s → P (Assert e s)) →
  (∀ (n : nat) (A : Type) (a : A) (s : stmt), P s → P (AnnotStmt n a s)) →
  (∀ (a : location_info) (s : stmt), P s → P (LocInfoS a s)) →
  (∀ s : lang.stmt, P (Stmt s)) → ∀ s : stmt, P s.
Proof.
  move => *. generalize dependent P => P. match goal with | s : stmt |- _ => revert s end.
  fix FIX 1. move => [ ^s] ?? Hswitch *. 3: {
    apply Hswitch; first by apply: FIX. elim: sbs; auto.
  }
  all: auto.
Qed.


Fixpoint to_stmt (s : stmt) : lang.stmt :=
  match s with
  | Goto b => lang.Goto b
  | Return e => lang.Return (to_expr e)
  | Switch it e m bs def => lang.Switch it (to_expr e) m (to_stmt <$> bs) (to_stmt def)
  | Assign o ly e1 e2 s => lang.Assign o ly (to_expr e1) (to_expr e2) (to_stmt s)
  | Call ret f args s => lang.Call ret (to_expr f) (to_expr <$> args) (to_stmt s)
  | SkipS s => lang.SkipS (to_stmt s)
  | StuckS => lang.StuckS
  | ExprS e s => lang.ExprS (to_expr e) (to_stmt s)
  | If e s1 s2 => (if: to_expr e then to_stmt s1 else to_stmt s2)%E
  | Assert e s => (assert: to_expr e; to_stmt s)%E
  | AnnotStmt n a s => notation.AnnotStmt n a (to_stmt s)
  | LocInfoS a s => notation.LocInfo a (to_stmt s)
  | Stmt s => s
  end.

Ltac of_stmt s :=
  lazymatch s with
  | [] => constr:(@nil stmt)
  | ?s :: ?ss =>
    let s := of_stmt s in
    let ss := of_stmt ss in
    constr:(s :: ss)

  | notation.AnnotStmt ?n ?a ?s =>
    let s := of_stmt s in
    constr:(AnnotStmt n a s)
  | notation.LocInfo ?a ?s =>
    let s := of_stmt s in
    constr:(LocInfoS a s)
  | (assert: ?e ; ?s)%E =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(Assert e s)
  | (if: ?e then ?s1 else ?s2)%E =>
    let e := of_expr e in
    let s1 := of_stmt s1 in
    let s2 := of_stmt s2 in
    constr:(If e s1 s2)
  | lang.Goto ?b => constr:(Goto b)
  | lang.Return ?e =>
    let e := of_expr e in constr:(Return e)
  | lang.Switch ?it ?e ?m ?bs ?def =>
    let e := of_expr e in
    let bs := of_stmt bs in
    let def := of_stmt def in
    constr:(Switch it e m bs def)
  | lang.Assign ?o ?ly ?e1 ?e2 ?s =>
    let e1 := of_expr e1 in
    let e2 := of_expr e2 in
    let s := of_stmt s in
    constr:(Assign o ly e1 e2 s)
  | lang.Call ?r ?f ?args ?s =>
    let f := of_expr f in
    let args := of_expr args in
    let s := of_stmt s in
    constr:(Call r f args s)
  | lang.SkipS ?s =>
    let s := of_stmt s in
    constr:(SkipS s)
  | lang.StuckS => constr:(StuckS s)
  | lang.ExprS ?e ?s =>
    let e := of_expr e in
    let s := of_stmt s in
    constr:(ExprS e s)
  | _ => constr:(Stmt s)
  end.

Inductive stmt_ectx :=
| AssignRCtx (o : order) (ly : layout) (e1 : expr) (s : stmt)
| AssignLCtx (o : order) (ly : layout) (v2 : val) (s : stmt)
| ReturnCtx
| SwitchCtx (it : int_type) (m: gmap Z nat) (bs : list stmt) (def : stmt)
| CallLCtx (r : var_name) (args : list expr) (s : stmt)
| CallRCtx (r : var_name) (f : val) (vl : list val) (el : list expr) (s : stmt)
| ExprSCtx (s : stmt)
| IfCtx (s1 s2 : stmt)
| AssertCtx (s : stmt)
.

Definition stmt_fill (Ki : stmt_ectx) (e : expr) : stmt :=
  match Ki with
  | AssignRCtx o ly e1 s => Assign o ly e1 e s
  | AssignLCtx o ly v2 s => Assign o ly e (Val v2) s
  | ReturnCtx => Return e
  | ExprSCtx s => ExprS e s
  | SwitchCtx it m bs def => Switch it e m bs def
  | CallLCtx r args s => Call r e args s
  | CallRCtx r f vl el s => Call r (Val f) ((Val <$> vl) ++ e :: el) s
  | IfCtx s1 s2 => If e s1 s2
  | AssertCtx s => Assert e s
  end.

Definition find_stmt_fill (s : stmt) : option (stmt_ectx * expr) :=
  match s with
  | Goto _ | Stmt _ | AnnotStmt _ _ _ | LocInfoS _ _ | SkipS _ | StuckS => None
  | Return e => if e is (Val v) then None else Some (ReturnCtx, e)
  | ExprS e s => if e is (Val v) then None else Some (ExprSCtx s, e)
  | Switch it e m bs def => if e is (Val v) then None else Some (SwitchCtx it m bs def, e)
  | Assign o ly e1 e2 s => if e2 is (Val v) then if e1 is (Val v) then None else Some (AssignLCtx o ly v s, e1) else Some (AssignRCtx o ly e1 s, e2)
  | Call ret f args s =>
    if f is (Val vf) then
      (* TODO: handle arguments here? Is a bit tricky since arguments are a list *)
      None
    else
      Some (CallLCtx ret args s, f)
  | If e s1 s2 => if e is (Val v) then None else Some (IfCtx s1 s2, e)
  | Assert e s => if e is (Val v) then None else Some (AssertCtx s, e)
  end.

Lemma find_stmt_fill_correct s Ks e:
  find_stmt_fill s = Some (Ks, e) → s = stmt_fill Ks e.
Proof.
  destruct s => *; repeat (try case_match; simpl in *; simplify_eq => //).
Qed.

Lemma stmt_fill_correct Ks:
  ∃ Ks', ∀ e, to_stmt (stmt_fill Ks e) = lang.stmt_fill Ks' (to_expr e).
Proof.
  move: Ks => [] *; [
               eexists (lang.AssignRCtx _ _ _ _)|
               eexists (lang.AssignLCtx _ _ _ _)|
               eexists (lang.ReturnCtx)|
               eexists (lang.SwitchCtx _ _ _ _)|
               eexists (lang.CallLCtx _ _ _)|
               eexists (lang.CallRCtx _ _ _ _ _)|
               eexists (lang.ExprSCtx _)|
               eexists (lang.SwitchCtx _ _ _ _)|
               eexists (lang.SwitchCtx _ _ _ _)|
               ..] => //= ?; f_equal;
                       by rewrite ?fmap_app to_expr_val_list.
Qed.

(*** Substitution *)
Fixpoint subst (x : var_name) (v : val) (e : expr)  : expr :=
  match e with
  | Var y => if bool_decide (y = x) then (Val v) else Var y
  | Loc l => Loc l
  | Val v => Val v
  | UnOp op ot e => UnOp op ot (subst x v e)
  | BinOp op ot1 ot2 e1 e2 => BinOp op ot1 ot2 (subst x v e1) (subst x v e2)
  | Deref o l e => Deref o l (subst x v e)
  | CAS ot e1 e2 e3 => CAS ot (subst x v e1) (subst x v e2) (subst x v e3)
  | Concat es => Concat (subst x v <$> es)
  | SkipE e => SkipE (subst x v e)
  | StuckE => StuckE
  | Use o ly e => Use o ly (subst x v e)
  | AddrOf e => AddrOf (subst x v e)
  | AnnotExpr n a e => AnnotExpr n a (subst x v e)
  | LocInfoE a e => LocInfoE a (subst x v e)
  | StructInit ly fs => StructInit ly (prod_map id (subst x v) <$> fs)
  | GetMember e s m => GetMember (subst x v e) s m
  | GetMemberUnion e ul m => GetMemberUnion (subst x v e) ul m
  | Expr e => Expr (lang.subst x v e)
  end.

Fixpoint subst_l (xs : list var_name) (vs : list val) (e : expr)  : expr :=
  match xs, vs with
  | x::xs', v::vs' => subst x v (subst_l xs' vs' e)
  | _, _ => e
  end.


Lemma to_expr_subst x v e :
  to_expr (subst x v e) = lang.subst x v (to_expr e).
Proof.
  elim: e => *//; cbn -[notation.GetMember]; (repeat case_bool_decide) => //=; f_equal; eauto.
  - (** Concat *)
    rewrite -!list_fmap_compose. apply list_fmap_ext' => //. by apply Forall_forall.
  - (** GetMember *)
    match goal with
    | _ : ?e1 = ?e2 |- _ => assert (e1 = e2) as -> by assumption
    end; done.
  - (** AnnotExpr *)
    match goal with
    | |- notation.AnnotExpr ?n _ _ = _ => generalize dependent n
    end.
    by rewrite /notation.AnnotExpr; elim; eauto => /= n ->.
  - (** StructInit *)
    match goal with | H : struct_layout |- _ => rename H into sl end.
    match goal with | H : list (string * expr) |- _ => rename H into fs end.
    rewrite /notation.StructInit; f_equal.
    generalize dependent fs.
    induction (sl_members sl) as [|[f ly] ? IHfs]; first done. move => fs Hf.
    rewrite fmap_cons IHfs //=; clear IHfs; f_equal.
    rewrite [X in _ = X]apply_default /=. f_equal. destruct f as [f|] => //=.
    rewrite !list_to_map_fmap !lookup_fmap. destruct (list_to_map fs !! f) as [e|] eqn:H; simpl; last done.
    f_equal. move: Hf => /Forall_forall IH. apply (IH _).
    simplify_eq. apply elem_of_list_to_map_2 in H. set_solver.
Qed.

Lemma to_expr_subst_l xs vs e :
  to_expr (subst_l xs vs e) = lang.subst_l xs vs (to_expr e).
Proof. elim: xs vs e => //= x xs IH [|v vs] // e. by rewrite to_expr_subst IH. Qed.

Fixpoint subst_stmt (xs : list var_name) (vs : list val) (s : stmt) : stmt :=
  match s with
  | Goto b => Goto b
  | Return e => Return (subst_l xs vs e)
  | Switch it e m' bs def => Switch it (subst_l xs vs e) m' (subst_stmt xs vs <$> bs) (subst_stmt xs vs def)
  | Assign o ly e1 e2 s => Assign o ly (subst_l xs vs e1) (subst_l xs vs e2) (subst_stmt xs vs s)
  | Call ret f args s =>
    (* TODO: remove ret from xs*)
    Call ret (subst_l xs vs f) (subst_l xs vs <$> args) (subst_stmt xs vs s)
  | SkipS s => SkipS (subst_stmt xs vs s)
  | StuckS => StuckS
  | ExprS e s => ExprS (subst_l xs vs e) (subst_stmt xs vs s)
  | If e s1 s2 => If (subst_l xs vs e) (subst_stmt xs vs s1) (subst_stmt xs vs s2)
  | Assert e s => Assert (subst_l xs vs e) (subst_stmt xs vs s)
  | AnnotStmt n a s => AnnotStmt n a (subst_stmt xs vs s)
  | LocInfoS a s => LocInfoS a (subst_stmt xs vs s)
  | Stmt s => Stmt (lang.subst_stmt xs vs s)
  end.

Lemma to_stmt_subst xs vs s :
  to_stmt (subst_stmt xs vs s) = lang.subst_stmt xs vs (to_stmt s).
Proof.
  elim: s => * //=; repeat rewrite to_expr_subst_l //; repeat f_equal => //; repeat rewrite -list_fmap_compose.
  - by apply Forall_fmap_ext_1.
  - apply list_fmap_ext => // ? /=. apply to_expr_subst_l.
  - match goal with
    | |- notation.AnnotStmt ?n _ _ = _ => generalize dependent n
    end.
    by rewrite /notation.AnnotStmt; elim; eauto => /= n ->.
Qed.
End W.

(** Substitution *)
(* TODO: make this not unfold AnnotStmt *)
Ltac simpl_subst :=
  simpl;
  repeat (match goal with
  | |- context [subst_stmt ?xs ?vs ?s] =>
      let s' := W.of_stmt s in
      change (subst_stmt xs vs s) with (subst_stmt xs vs (W.to_stmt s'));
      rewrite <-(W.to_stmt_subst xs); simpl (* ssr rewrite is slower *)
  end; unfold W.to_stmt, W.to_expr; simpl).
Arguments W.to_expr : simpl never.
Arguments W.to_stmt : simpl never.
Arguments subst : simpl never.
Arguments subst_l : simpl never.
Arguments subst_stmt : simpl never.

Lemma stmt_fill_call_inv Ks e r vf vs s :
  stmt_fill Ks e = (r <- Val vf with Val <$> vs; s)%E → ∃ v, e = Val v.
Proof.
  destruct Ks; simpl => Heq; simplify_eq; eauto.
  generalize dependent vl => vl.
  elim: vl vs; csimpl. 1: by destruct vs => //= [[]]; eauto.
  move => ?? IH [|??] //; csimpl => [[]]. eauto.
Qed.


Ltac inv_stmt_step :=
   match goal with
  | H : stmt_step (update_stmt _ ?st) _ _ _ _ _ |- _ =>
    inversion H; subst; clear H; simplify_map_eq/=;
      match goal with
      | H2 : st = ?e2 |- _ =>
         match st with
         | stmt_fill ?Ks ?e =>
               try by [destruct (stmt_fill_call_inv _ _ _ _ _ _ H2); simplify_eq];
               try by [destruct Ks; simpl in *; simplify_eq];
               have [||??]:= (stmt_fill_inj _ _ _ _ _ _ H2); eauto using language.val_stuck; subst
         | _ =>
           try (destruct (stmt_fill_call_inv _ _ _ _ _ _ (eq_sym H2)); simplify_eq);
           try (match e2 with
                  | stmt_fill ?Ks ?e => destruct Ks; simpl in *; simplify_eq
                end
             );
           try (match goal with
                  | H : prim_step (Val _) _ _ _ _ _ |- _ => exfalso; eapply (val_irreducible); [| apply H]; eauto
                end
             )
         end
      | |- _ => idtac
      end
   end.

Ltac inv_expr_step :=
  repeat match goal with
  | _ => progress simplify_map_eq/= (* simplify memory stuff *)
  | H : to_val _ = Some _ |- _ => apply of_to_val in H
  | H : context [to_val (of_val _)] |- _ => rewrite to_of_val in H
  | H : expr_step ?e _ _ _ _ _ |- _ =>
     try (is_var e; fail 1); (* inversion yields many goals if [e] is a variable
     and can thus better be avoided. *)
     inversion H; subst; clear H
  end.

Ltac solve_struct_obligations :=
  try done; do ! constructor; set_solver.
