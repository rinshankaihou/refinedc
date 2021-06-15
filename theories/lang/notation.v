From refinedc.lang Require Export lang.
Set Default Proof Using "Type".

Coercion val_of_loc : loc >-> val.
Coercion Val : val >-> expr.
Coercion Var : var_name >-> expr.
Definition string_to_varname (s : string) : var_name := s.
Coercion string_to_varname : string >-> var_name.
Coercion it_layout : int_type >-> layout.
Notation "☠" := MPoison : val_scope.
Notation "!{ ly , o } e" := (Deref o ly e%E) (at level 9, format "!{ ly ,  o } e") : expr_scope.
Notation "!{ ly } e" := (Deref Na1Ord ly e%E) (at level 9, format "!{ ly } e") : expr_scope.
(* − is a unicode minus, not the normal minus to prevent parsing conflicts *)
Notation "'−' '{' ot } e" := (UnOp NegOp ot e%E)
  (at level 40, format "'−' '{' ot }  e") : expr_scope.
Notation "e1 '+' '{' ot1 , ot2 } e2" := (BinOp AddOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '+' '{' ot1 ,  ot2 }  e2") : expr_scope.
(* This conflicts with rewrite -{2}(app_nil_r vs). *)
Notation "e1 '-' '{' ot1 , ot2 } e2" := (BinOp SubOp ot1 ot2 e1%E e2%E)
  (at level 50, left associativity, format "e1  '-' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '=' '{' ot1 , ot2 } e2" := (BinOp EqOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '=' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 '!=' '{' ot1 , ot2 } e2" := (BinOp NeOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  '!=' '{' ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ≤{ ot1 , ot2 } e2" := (BinOp LeOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≤{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 <{ ot1 , ot2 } e2" := (BinOp LtOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  <{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 ≥{ ot1 , ot2 } e2" := (BinOp GeOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  ≥{ ot1 ,  ot2 }  e2") : expr_scope.
Notation "e1 >{ ot1 , ot2 } e2" := (BinOp GtOp ot1 ot2 e1%E e2%E)
  (at level 70, format "e1  >{ ot1 ,  ot2 }  e2") : expr_scope.
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
(* The unicode ← is already part of the notation "_ ← _; _" for bind. *)
Notation "e1 <-{ ly , o } e2 ; s" := (Assign o ly e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ly ',' o '}'  e2 ';' '/' s ']'") : expr_scope.
Notation "e1 <-{ ly } e2 ; s" := (Assign Na1Ord ly e1%E e2%E s%E)
  (at level 80, s at level 200, format "'[v' e1  '<-{' ly '}'  e2 ';' '/' s ']'") : expr_scope.
Notation "'if:' e1 'then' s1 'else' s2" := (Switch bool_it e1%E {[ 0 := 0%nat ]} [s2%E] s1%E)
  (at level 102, e1, s1, s2 at level 150, format "'[v' 'if:'  e1  'then' '/  ' s1 '/' 'else' '/  ' s2 ']'") : expr_scope.
Notation "'expr:' e ; s" := (ExprS e%E s%E)
  (at level 80, s at level 200, format "'[v' 'expr:'  e ';' '/' s ']'") : expr_scope.

Definition Assert (e : expr) (s : stmt) : stmt := (if: e then s else StuckS)%E.
Notation "'assert:' e ; s" := (Assert e%E s%E)
  (at level 80, s at level 200, format "'[v' 'assert:'  e ';' '/' s ']'") : expr_scope.
Arguments Assert : simpl never.
Typeclasses Opaque Assert.

Definition Use (o : order) (ly : layout) (e : expr) := Deref o ly e.
Notation "'use{' ly , o } e" := (Use o ly e%E) (at level 9, format "'use{' ly ,  o }  e") : expr_scope.
Notation "'use{' ly } e" := (Use Na1Ord ly e%E) (at level 9, format "'use{' ly }  e") : expr_scope.
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
Definition void_layout : layout := {| ly_size := 0; ly_align_log := 0 |}.

Definition void_ptr : layout := {| ly_size := bytes_per_addr; ly_align_log := bytes_per_addr_log |}.
Notation "'void*'" := (void_ptr).

Definition VOID : val := [].

Definition field_list := list (option var_name * layout).

Definition field_names (s : field_list) : list var_name := omap fst s.
Definition offset_of_idx (s : field_list) (i : nat) : nat :=
  sum_list (take i (ly_size <$> s.*2)).
Definition index_of (s : field_list) (n : var_name) : option nat :=
  fst <$> list_find (λ x, x.1 = Some n) s.
Definition offset_of (s : field_list) (n : var_name) : option nat :=
  (λ idx, offset_of_idx s idx) <$> index_of s n.
Definition field_idx_of_idx (s : field_list) (i : nat) : nat :=
  length (field_names (take i s)).
Fixpoint field_index_of (s : field_list) (n : var_name) : option nat :=
  match s with
  | [] => None
  | (n', ly)::s' => if bool_decide (n' = Some n) then Some 0%nat else
                    (if n' is Some _ then S else id) <$> field_index_of s' n
  end.
Fixpoint pad_struct {A} (s : field_list) (l : list A) (f : layout → A) : list A :=
  match s with
  | [] => []
  | (n, ly)::s' => (if n is Some _ then default (f ly) (head l) else f ly)::pad_struct s' (if n is Some _ then tail l else l) f
  end.
Fixpoint check_fields_aligned (s : field_list) (pos : nat) : bool :=
  match s with
  | [] => true
  | (_,ly)::s' => bool_decide (pos `mod` ly_align ly = 0) && check_fields_aligned s' (pos + ly.(ly_size))
  end.

Record struct_layout := {
   sl_members : field_list;
   sl_nodup : bool_decide (NoDup (field_names sl_members));
   sl_size : sum_list (ly_size <$> sl_members.*2) < max_int size_t + 1;
   sl_fields_aligned : check_fields_aligned sl_members 0 = true;
}.

Definition StructInit (ly : struct_layout) (fs : list (string * expr)) : expr :=
  let fs : gmap string expr := list_to_map fs in
  let fn idly := default (Val (replicate (ly_size idly.2) MPoison)) (x ← idly.1; fs !! x) in
  Concat (fn <$> sl_members ly).
Typeclasses Opaque StructInit.
Arguments StructInit : simpl never.

Definition layout_of (s : struct_layout) : layout := {|
  ly_size := sum_list (ly_size <$> s.(sl_members).*2);
  ly_align_log := max_list (ly_align_log <$> s.(sl_members).*2)
|}.

Coercion layout_of : struct_layout >-> layout.

Lemma struct_layout_eq sl1 sl2 :
  sl1.(sl_members) = sl2.(sl_members) →
  sl1 = sl2.
Proof. destruct sl1, sl2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma index_of_cons n n' ly s:
  index_of ((n',ly)::s) n = (if decide (n' = Some n) then Some 0%nat else S <$> index_of s n).
Proof. cbn. case_decide => //. rewrite /index_of -!option_fmap_compose. apply option_fmap_ext. by case. Qed.

Lemma field_index_of_leq s n i:
  field_index_of s n = Some i →
  (i < length (field_names s))%nat.
Proof.
  elim: s i => //= -[??]? IH i /= Hf. case_bool_decide; simplify_eq => //=; first lia.
  move: Hf => /fmap_Some[?[Hf ?]]; subst. case_match => /=; naive_solver lia.
Qed.

Lemma field_index_of_to_index_of n s i:
  field_index_of s n = Some i →
  is_Some (index_of s n).
Proof.
  rewrite /index_of.
  elim: s i => // -[n' ly] s IH i/=. case_decide; case_bool_decide => //=; eauto.
  destruct n' => /fmap_Some[x [? _]]; have [|? /fmap_Some[?[->?]]] := IH x; eauto.
Qed.

Lemma pad_struct_lookup_field {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  l !! i = Some x →
  pad_struct s l f !! j = Some x.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j/= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst.
  by case_match; destruct l => //=; apply: IH.
Qed.

Lemma pad_struct_insert_field {A} s (l : list A) f i j n x :
  index_of s n = Some j →
  field_index_of s n = Some i →
  (i < length l)%nat →
  <[j:=x]> (pad_struct s l f) = pad_struct s (<[i:=x]> l) f.
Proof.
  elim: s l i j => // -[n' ly] s IH l i j /= Hin Hf ?. rewrite index_of_cons in Hin.
  case_bool_decide; case_decide => //; simplify_eq; first by destruct l; naive_solver lia.
  move: Hin Hf => /fmap_Some[j'[??]] /fmap_Some[?[??]]; subst. destruct l; first by naive_solver lia.
  case_match => /=; f_equal; apply IH; naive_solver lia.
Qed.

Lemma pad_struct_snoc_Some {A} s n ly ls (l : A) f :
  length (field_names s) = length ls →
  pad_struct (s ++ [(Some n, ly)]) (ls ++ [l]) f = pad_struct s ls f ++ [l].
Proof.
  elim: s ls => /=. by destruct ls.
  move => -[n' ly'] s IH ls /=. case_match.
  - destruct ls => //= -[?]. f_equal. by apply IH.
  - move => ?. f_equal. by apply IH.
Qed.

Lemma pad_struct_snoc_None {A} s ly (ls : list A) f :
  pad_struct (s ++ [(None, ly)]) ls f = pad_struct s ls f ++ [f ly].
Proof. elim: s ls => //=. move => -[n' ly'] s IH ls /=. f_equal. by apply IH. Qed.

Lemma offset_of_cons' n n' ly s:
  offset_of ((n', ly)::s) n = (if decide (n' = Some n) then Some 0 else (λ m, ly_size ly + m) <$> (offset_of s n))%nat.
Proof. rewrite /offset_of/= index_of_cons. case_decide => //=. destruct (index_of s n) eqn: Hfind => //=. Qed.

Lemma offset_of_cons n n' ly s:
  n' = Some n ∨ n ∈ field_names s →
  default 0%nat (offset_of ((n', ly)::s) n) = (if decide (n' = Some n) then 0 else ly_size ly + (default 0%nat (offset_of s n)))%nat.
Proof.
  rewrite /offset_of/= index_of_cons. case_decide => //= -[|/elem_of_list_omap[x Hin]]//.
  destruct (index_of s n) eqn: Hfind => //=.
  move: Hfind => /fmap_None/list_find_None /Forall_forall Hfind. set_solver.
Qed.

Lemma offset_of_from_in m s:
  Some m ∈ s.*1 → ∃ n, offset_of s m = Some n.
Proof.
  elim: s. set_solver.
  move => [??]? IH. rewrite offset_of_cons'. csimpl => ?.
  case_decide => //; [ naive_solver |].
  have [|? ->]:= IH. by set_solver.
  naive_solver.
Qed.

Lemma offset_of_idx_le_size sl i:
  (offset_of_idx (sl_members sl) i ≤ ly_size sl)%nat.
Proof. apply: sum_list_with_take. Qed.

Lemma offset_of_bound i sl:
  offset_of_idx sl.(sl_members) i ≤ max_int size_t.
Proof.
  have ?:= sl_size sl.
  enough (offset_of_idx (sl_members sl) i ≤ sum_list (ly_size <$> (sl_members sl).*2)) by lia.
  by apply Nat2Z.inj_le, sum_list_with_take.
Qed.

Fixpoint check_fields_aligned_alt (s : field_list) (l : loc) : Prop :=
  match s with
  | [] => True
  | (_,ly)::s' => l `has_layout_loc` ly ∧ check_fields_aligned_alt s' (l +ₗ ly.(ly_size))
  end.

Lemma check_fields_aligned_alt_correct sl l:
  l `has_layout_loc` layout_of sl →
  check_fields_aligned_alt sl.(sl_members) l.
Proof.
  rewrite /layout_of.
  have := sl_fields_aligned sl. rewrite -{2}[l]shift_loc_0_nat. move: O => off.
  elim: (sl_members sl) off => // -[n ly] s IH; csimpl => off /andb_true_iff[/bool_decide_eq_true/Z.mod_divide Hdiv ?]?.
  split.
  - apply aligned_to_offset.
    + apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
    + apply Hdiv. have ->: 0 = O by []. move => /Nat2Z.inj/Nat.pow_nonzero. lia.
  - rewrite shift_loc_assoc_nat. apply IH => //. apply: has_layout_loc_trans => //. rewrite /ly_align_log. lia.
Qed.

Definition GetMember (e : expr) (s : struct_layout) (m : var_name) : expr :=
  (e at_offset{u8, PtrOp, IntOp size_t} Val (default [MPoison] (offset_of s.(sl_members) m ≫= (λ m, val_of_Z (Z.of_nat m) size_t))))%E.
Notation "e 'at{' s } m" := (GetMember e%E s m) (at level 10, format "e  'at{' s }  m") : expr_scope.
Typeclasses Opaque GetMember.
Arguments GetMember : simpl never.

Definition GetMemberLoc (l : loc) (s : struct_layout) (m : var_name) : loc :=
  (l +ₗ Z.of_nat (default 0%nat (offset_of s.(sl_members) m)))%E.
Notation "l 'at{' s '}ₗ' m" := (GetMemberLoc l s m) (at level 10, format "l  'at{' s '}ₗ'  m") : stdpp_scope.
Typeclasses Opaque GetMemberLoc.
Arguments GetMemberLoc : simpl never.

Definition OffsetOf (s : struct_layout) (m : var_name) : expr :=
  (default StuckE (Val <$> (offset_of s.(sl_members) m) ≫= (λ m, val_of_Z (Z.of_nat m) size_t)))%E.
Typeclasses Opaque OffsetOf.
Arguments OffsetOf : simpl never.

Record union_layout := {
   ul_members : list (var_name * layout);
   ul_nodup : bool_decide (NoDup ul_members.*1);
   ul_size : max_list (ly_size <$> ul_members.*2) < max_int size_t + 1;
}.

Definition ul_layout (ul : union_layout) : layout := {|
  ly_size := max_list (ly_size <$> ul.(ul_members).*2);
  ly_align_log := max_list (ly_align_log <$> ul.(ul_members).*2)
|}.
Coercion ul_layout : union_layout >-> layout.

Definition index_of_union (n : var_name) (ul : union_layout) : option nat :=
  fst <$> list_find (λ x, x.1 = n) ul.(ul_members).

Definition layout_of_union_member (n : var_name) (ul : union_layout) : option layout :=
  i ← index_of_union n ul; (snd <$> ul.(ul_members) !! i).

Lemma union_layout_eq ul1 ul2 :
  ul1.(ul_members) = ul2.(ul_members) →
  ul1 = ul2.
Proof. destruct ul1, ul2 => /= ?. subst. f_equal; apply: proof_irrel. Qed.

Lemma layout_of_union_member_in_ul n ul ly:
  layout_of_union_member n ul = Some ly →
  ly ∈ ul.(ul_members).*2.
Proof.
  rewrite /layout_of_union_member. destruct (index_of_union n ul) => //= Hin.
  apply: elem_of_list_lookup_2. by rewrite list_lookup_fmap.
Qed.

Lemma index_of_union_lookup ul i n ly:
  ul.(ul_members) !! i = Some (n, ly) →
  index_of_union n ul = Some i.
Proof.
  move => H1. apply fmap_Some. exists (i, (n, ly)). split => //.
  apply list_find_Some. split_and! => // j[??]H2? /=?. subst.
  suff : (i = j) by lia. apply: NoDup_lookup.
  { eapply bool_decide_spec. apply (ul_nodup ul). }
  all: rewrite list_lookup_fmap; apply fmap_Some; naive_solver.
Qed.

Definition GetMemberUnion (e : expr) (ul : union_layout) (m : var_name) : expr := (e)%E.
Notation "e 'at_union{' ul } m" := (GetMemberUnion e%E ul m) (at level 10, format "e  'at_union{' ul }  m") : expr_scope.
Typeclasses Opaque GetMemberUnion.
Arguments GetMemberUnion : simpl never.

Definition GetMemberUnionLoc (l : loc) (ul : union_layout) (m : var_name) : loc := (l)%E.
Notation "l 'at_union{' ul '}ₗ' m" := (GetMemberUnionLoc l ul m) (at level 10, format "l  'at_union{' ul '}ₗ'  m") : stdpp_scope.
Typeclasses Opaque GetMemberUnionLoc.
Arguments GetMemberUnionLoc : simpl never.

Definition OffsetOfUnion (ul : union_layout) (m : var_name) : expr := (i2v 0 size_t).
Typeclasses Opaque OffsetOfUnion.
Arguments OffsetOfUnion : simpl never.

Definition mk_array_layout := ly_mult.
Typeclasses Opaque mk_array_layout.

(*** Tests *)
Example test1 (l : loc) ly :
  (l <-{ly} use{ly}(&l +{PtrOp, IntOp size_t} (l ={PtrOp, PtrOp} l)); ExprS (Call l [ (l : expr); (l : expr)]) (l <-{ly, ScOrd} l; Goto "a"))%E =
  (Assign Na1Ord ly l (Use Na1Ord ly (BinOp AddOp PtrOp (IntOp size_t) (AddrOf l) (BinOp EqOp PtrOp PtrOp l l))))
      (ExprS (Call l [ Val (val_of_loc l); Val (val_of_loc l)]) ((Assign ScOrd ly l l) (Goto "a"))).
Proof. simpl. reflexivity. Abort.

Example test_if (l : loc) :
  (if: l then Goto "a" else Goto "b")%E = (Switch bool_it l {[ 0 := 0%nat ]} [Goto "b"] (Goto "a")).
Proof. reflexivity. Abort.

Example test_get_member (l : loc) (s : struct_layout) :
  (!{s} (!{s, ScOrd} l) at{s} "a")%E = GetMember (Deref Na1Ord s (Deref ScOrd s l%E)) s "a".
Proof. simpl. reflexivity. Abort.
