From caesium Require Export lang.
Set Default Proof Using "Type".

Coercion val_of_loc : loc >-> val.
Coercion Val : val >-> expr.
Coercion Var : var_name >-> expr.
Definition string_to_varname (s : string) : var_name := s.
Coercion string_to_varname : string >-> var_name.
Coercion it_layout : int_type >-> layout.
Notation "☠" := MPoison : val_scope.
Notation "!{ ot , o } e" := (Deref o ot e%E) (at level 9, format "!{ ot ,  o } e") : expr_scope.
Notation "!{ ot } e" := (Deref Na1Ord ot e%E) (at level 9, format "!{ ot } e") : expr_scope.
(* − is a unicode minus, not the normal minus to prevent parsing conflicts *)
Notation "'−' '{' ot } e" := (UnOp NegOp ot e%E)
  (at level 40, format "'−' '{' ot }  e") : expr_scope.
Notation "e1 '+' '{' ot1 , ot2 } e2" := (BinOp AddOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '+' '{' ot1 ,  ot2 }  e2") : expr_scope.
(* This conflicts with rewrite -{2}(app_nil_r vs). *)
Notation "e1 '-' '{' ot1 , ot2 } e2" := (BinOp SubOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '-' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '=' '{' ot1 , ot2 , rit } e2" := (BinOp (EqOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '=' '{' ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 '!=' '{' ot1 , ot2 , rit } e2" := (BinOp (NeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '!=' '{' ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ≤{ ot1 , ot2 , rit } e2" := (BinOp (LeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≤{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 <{ ot1 , ot2 , rit } e2" := (BinOp (LtOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  <{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ≥{ ot1 , ot2 , rit } e2" := (BinOp (GeOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≥{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 >{ ot1 , ot2 , rit } e2" := (BinOp (GtOp rit) ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  >{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Notation "e1 ×{ ot1 , ot2 } e2" := (BinOp MulOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ×{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 /{ ot1 , ot2 } e2" := (BinOp DivOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  /{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 %{ ot1 , ot2 } e2" := (BinOp ModOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  %{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 <<{ ot1 , ot2 } e2" := (BinOp ShlOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  <<{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 >>{ ot1 , ot2 } e2" := (BinOp ShrOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  >>{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 &{ ot1 , ot2 } e2" := (BinOp AndOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  &{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 |{ ot1 , ot2 } e2" := (BinOp OrOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  |{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ^{ ot1 , ot2 } e2" := (BinOp XorOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ^{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ,{ ot1 , ot2 } e2" := (BinOp Comma ot1 ot2 e1%E e2%E)
  (at level 30, format "e1  ,{ ot1 ,  ot2 }  e2") : expr_scope.
(* The offset must be evaluated first for the type system to work, thus the order is switched here. *)
Notation "e1 'at_offset{' ly , ot1 , ot2 } e2" := (BinOp (PtrOffsetOp ly) ot2 ot1 e2%E e1%E)
  (at level 70, format "e1  at_offset{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 'at_neg_offset{' ly , ot1 , ot2 } e2" := (BinOp (PtrNegOffsetOp ly) ot2 ot1 e2%E e1%E)
  (at level 70, format "e1  at_neg_offset{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 'sub_ptr{' ly , ot1 , ot2 } e2" := (BinOp (PtrDiffOp ly) ot2 ot1 e1%E e2%E)
  (at level 70, format "e1  sub_ptr{ ly ,  ot1 ,  ot2 }  e2") : expr_scope.
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <-{ ot , o } e2 ; s" := (Assign o ot e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ot ',' o '}'  e2 ';' '/' s ']'") : expr_scope.
Notation "e1 <-{ ot } e2 ; s" := (Assign Na1Ord ot e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ot '}'  e2 ';' '/' s ']'") : expr_scope.
Notation "'if{' ot '}' ':' e1 'then' s1 'else' s2" := (IfS ot e1%E s1%E s2%E)
  (at level 102, e1, s1, s2 at level 150, format "'[v' 'if{' ot '}' ':'  e1  'then' '/  ' s1 '/' 'else' '/  ' s2 ']'") : expr_scope.
Notation "'expr:' e ; s" := (ExprS e%E s%E)
  (at level 80, s at level 200, format "'[v' 'expr:'  e ';' '/' s ']'") : expr_scope.

Definition LogicalAnd (ot1 ot2 : op_type) rit (e1 e2 : expr) : expr :=
  (IfE ot1 e1 (IfE ot2 e2 (i2v 1 rit) (i2v 0 rit)) (i2v 0 rit)).
Notation "e1 &&{ ot1 , ot2 , rit } e2" := (LogicalAnd ot1 ot2 rit e1 e2)
  (at level 70, format "e1  &&{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Arguments LogicalAnd : simpl never.
Typeclasses Opaque LogicalAnd.

Definition LogicalOr (ot1 ot2 : op_type) rit (e1 e2 : expr) : expr :=
  (IfE ot1 e1 (i2v 1 rit) (IfE ot2 e2 (i2v 1 rit) (i2v 0 rit))).
Notation "e1 ||{ ot1 , ot2 , rit } e2" := (LogicalOr ot1 ot2 rit e1 e2)
  (at level 70, format "e1  ||{ ot1 ,  ot2 , rit }  e2") : expr_scope.
Arguments LogicalOr : simpl never.
Typeclasses Opaque LogicalOr.

Definition Assert (ot : op_type) (e : expr) (s : stmt) : stmt := (if{ ot }: e then s else StuckS)%E.
Notation "'assert{' ot '}' ':' e ; s" := (Assert ot e%E s%E)
  (at level 80, s at level 200, format "'[v' 'assert{' ot '}' ':'  e ';' '/' s ']'") : expr_scope.
Arguments Assert : simpl never.
Typeclasses Opaque Assert.

Definition Use (o : order) (ot : op_type) (e : expr) := Deref o ot e.
Notation "'use{' ot , o } e" := (Use o ot e%E) (at level 9, format "'use{' ot ,  o }  e") : expr_scope.
Notation "'use{' ot } e" := (Use Na1Ord ot e%E) (at level 9, format "'use{' ot }  e") : expr_scope.
Arguments Use : simpl never.
Typeclasses Opaque Use.

Definition AddrOf (e : expr) := e.
(* TODO: this breaks the sigT notation { A : Type & (A -> nat) }. See if we can do something about it. *)
Notation "& e" := (AddrOf e%E) (at level 9, format "& e") : expr_scope.
Arguments AddrOf : simpl never.
Typeclasses Opaque AddrOf.

Definition LValue (e : expr) := e.
Arguments LValue : simpl never.
Typeclasses Opaque LValue.

Definition AnnotExpr (n : nat) {A} (a : A) (e : expr) := Nat.iter n SkipE e.
Arguments AnnotExpr : simpl never.
Typeclasses Opaque AnnotExpr.
Definition AnnotStmt (n : nat) {A} (a : A) (s : stmt) := Nat.iter n SkipS s.
Notation "'annot:' a ; s" := (AnnotStmt 0%nat a s%E)
  (at level 80, s at level 200, format "'annot:'  a ;  s") : expr_scope.
Arguments AnnotStmt : simpl never.
Typeclasses Opaque AnnotStmt.

Inductive location_info :=
| LocationInfo (file : string) (line_start column_start line_end column_end : Z).

Definition LocInfo {B} (a : location_info) (b : B) := b.
Arguments LocInfo : simpl never.
Typeclasses Opaque LocInfo.
Notation "'locinfo:' a ; b" := (LocInfo (B:=stmt) a b%E)
  (at level 80, b at level 200, format "'[v' 'locinfo:'  a ';' '/' b ']'") : expr_scope.
Notation LocInfoE := (LocInfo (B:=expr)).

Definition MacroE (m : list expr → expr) (es : list expr) := m es.
Arguments MacroE : simpl never.
Typeclasses Opaque MacroE.

(* One could probably get rid of this type class by swallowing the
substitutions in MacroE, i.e. make it parametrized by a list of names
and a list of expressions which are substituted in m. (Then one can
maybe also get rid of es?) *)
Class MacroWfSubst (m : list expr → expr) : Prop :=
  macro_wf_subst x v es: subst x v (m es) = m (subst x v <$> es)
.

(* Like [MacroE m es] but checks that [m es] is equal to [e] *)
Notation CheckedMacroE m es e := (ltac:(
   let rec get_head e := match e with
                         | ?f ?a => get_head f
                         | ?x => x
                         end in
   let mhead := get_head constr:(m%function) in
   let munf := (eval unfold mhead in (m%function)) in
   let esunf := (eval unfold LocInfo in (es%list)) in
   let eunf := (eval unfold LocInfo in e) in
   (* idtac munf; *)
   unify (munf esunf) eunf with typeclass_instances;
   exact (MacroE m es))) (only parsing).


Lemma annot_expr_S {A} n (a : A) e:
  AnnotExpr (S n) a e = SkipE (AnnotExpr n a e).
Proof. done. Qed.
Lemma annot_expr_S_r {A} n (a : A) e:
  AnnotExpr (S n) a e = (AnnotExpr n a (SkipE e)).
Proof. by rewrite /AnnotExpr Nat_iter_S_r. Qed.
Lemma annot_stmt_S {A} n (a : A) s:
  AnnotStmt (S n) a s = SkipS (AnnotStmt n a s).
Proof. done. Qed.
Lemma annot_stmt_S_r {A} n (a : A) s:
  AnnotStmt (S n) a s = (AnnotStmt n a (SkipS s)).
Proof. by rewrite /AnnotStmt Nat_iter_S_r. Qed.

(*** Layouts and structs *)
Definition StructInit (ly : struct_layout) (fs : list (string * expr)) : expr :=
  let fs : gmap string expr := list_to_map fs in
  let fn idly := default (Val (replicate (ly_size idly.2) MPoison)) (x ← idly.1; fs !! x) in
  Concat (fn <$> sl_members ly).
Typeclasses Opaque StructInit.
Arguments StructInit : simpl never.

Definition GetMember (e : expr) (s : struct_layout) (m : var_name) : expr :=
  (e at_offset{u8, PtrOp, IntOp size_t} Val (default [MPoison] (offset_of s.(sl_members) m ≫= (λ m, val_of_Z (Z.of_nat m) size_t None))))%E.
Notation "e 'at{' s } m" := (GetMember e%E s m) (at level 10, format "e  'at{' s }  m") : expr_scope.
Typeclasses Opaque GetMember.
Arguments GetMember : simpl never.

Definition OffsetOf (s : struct_layout) (m : var_name) : expr :=
  (default StuckE (Val <$> (offset_of s.(sl_members) m) ≫= (λ m, val_of_Z (Z.of_nat m) size_t None)))%E.
Typeclasses Opaque OffsetOf.
Arguments OffsetOf : simpl never.

Definition GetMemberUnion (e : expr) (ul : union_layout) (m : var_name) : expr := (e)%E.
Notation "e 'at_union{' ul } m" := (GetMemberUnion e%E ul m) (at level 10, format "e  'at_union{' ul }  m") : expr_scope.
Typeclasses Opaque GetMemberUnion.
Arguments GetMemberUnion : simpl never.

Definition OffsetOfUnion (ul : union_layout) (m : var_name) : expr := (i2v 0 size_t).
Typeclasses Opaque OffsetOfUnion.
Arguments OffsetOfUnion : simpl never.

(*** Tests *)
Example test1 (l : loc) ly ot :
  (l <-{ly} use{ot}(&l +{PtrOp, IntOp size_t} (l ={PtrOp, PtrOp, i32} l)); ExprS (Call l [ (l : expr); (l : expr)]) (l <-{ly, ScOrd} l; Goto "a"))%E =
  (Assign Na1Ord ly l (Use Na1Ord ot (BinOp AddOp PtrOp (IntOp size_t) (AddrOf l) (BinOp (EqOp i32) PtrOp PtrOp l l))))
      (ExprS (Call l [ Val (val_of_loc l); Val (val_of_loc l)]) ((Assign ScOrd ly l l) (Goto "a"))).
Proof. simpl. reflexivity. Abort.

Example test_get_member (l : loc) (s : struct_layout) ot :
  (!{ot} (!{ot, ScOrd} l) at{s} "a")%E = GetMember (Deref Na1Ord ot (Deref ScOrd ot l%E)) s "a".
Proof. simpl. reflexivity. Abort.
