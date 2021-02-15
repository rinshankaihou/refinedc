From refinedc.lang Require Import proofmode.
From refinedc.typing Require Export type.
Set Default Proof Using "Type".

Section judgements.
  Context `{!typeG Σ}.

  Class Learnable (P : iProp Σ) := {
    learnable_data : iProp Σ;
    learnable_learn : P -∗ □ learnable_data;
  }.

  Class LearnAlignment (β : own_state) (ty : type) := {
    learnalign_align : nat;
    learnalign_learn l : l ◁ₗ{β} ty -∗ ⌜l `aligned_to` learnalign_align⌝
  }.

  Class SimplifyHypPlace (l : loc) (β : own_state) (ty : type) (n : option N) : Type :=
    simplify_hyp_place :> SimplifyHyp (l ◁ₗ{β} ty) n.
  Class SimplifyHypVal (v : val) (ty : type) `{!Movable ty} (n : option N) : Type :=
    simplify_hyp_val :> SimplifyHyp (v ◁ᵥ ty) n.

  Class SimplifyGoalPlace (l : loc) (β : own_state) (ty : type) (n : option N) : Type :=
    simplify_goal_place :> SimplifyGoal (l ◁ₗ{β} ty) n.
  Class SimplifyGoalVal (v : val) (ty : type) `{!Movable ty} (n : option N) : Type :=
    simplify_goal_val :> SimplifyGoal (v ◁ᵥ ty) n.

  Class SubsumePlace (l : loc) (β : own_state) (ty1 ty2 : type) : Type :=
    subsume_place :> Subsume (l ◁ₗ{β} ty1) (l ◁ₗ{β} ty2).
  Class SubsumeVal (v : val) (ty1 ty2 : type) `{!Movable ty1} `{!Movable ty2} : Type :=
    subsume_val :> Subsume (v ◁ᵥ ty1) (v ◁ᵥ ty2).

  (* Variants of Subsume which don't need the continuation. P is an
  additional sidecondition. Not via iProp_to_Prop since there is no
  continuation. *)
  Class SimpleSubsumePlace (ty1 ty2 : type) (P : iProp Σ) : Prop :=
    simple_subsume_place l β: P -∗ l ◁ₗ{β} ty1 -∗ l ◁ₗ{β} ty2.
  Class SimpleSubsumePlaceR (ty1 ty2 : rtype) (x1 : ty1.(rty_type)) (x2 : ty2.(rty_type)) (P : iProp Σ) : Prop :=
    simple_subsume_place_r l β: P -∗ l ◁ₗ{β} x1 @ ty1 -∗ l ◁ₗ{β} x2 @ ty2.
  (* TODO: add infrastructure like SimpleSubsumePlaceR to
  SimpleSubsumeVal. Not sure if it would work because of the movable
  instance. *)
  Class SimpleSubsumeVal (ty1 ty2 : type) `{!Movable ty1} `{!Movable ty2} (P : iProp Σ) : Prop :=
    simple_subsume_val v: P -∗ v ◁ᵥ ty1 -∗ v ◁ᵥ ty2.

  (* This is similar to simplify hyp place (Some 0), but targeted at
  Copy and applying all simplifications at once instead of step by
  step. We need this because copying duplicates a type and we want to
  make it as specific as we can before we do the duplication (e.g.
  destruct all existentials in it). *)
  Definition copy_as (l : loc) (β : own_state) (ty : type) (T : mtype → iProp Σ) : iProp Σ :=
    l ◁ₗ{β} ty -∗ ∃ ty' : mtype, l ◁ₗ{β} ty' ∗ ⌜Copyable ty'⌝ ∗ T ty'.
  Class CopyAs (l : loc) (β : own_state) (ty : type) : Type :=
    copy_as_proof T : iProp_to_Prop (copy_as l β ty T).

  (* A is the annotation from the code *)
  Definition typed_annot_expr (n : nat) {A} (a : A) (v : val) (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
    (P ={⊤}[∅]▷=∗^n |={⊤}=> T).
  Class TypedAnnotExpr (n : nat) {A} (a : A) (v : val) (P : iProp Σ) : Type :=
    typed_annot_expr_proof T : iProp_to_Prop (typed_annot_expr n a v P T).

  Definition typed_annot_stmt {A} (a : A) (l : loc) (P : iProp Σ) (T : iProp Σ) : iProp Σ :=
    (P ={⊤}[∅]▷=∗ T).
  Class TypedAnnotStmt {A} (a : A) (l : loc) (P : iProp Σ) : Type :=
    typed_annot_stmt_proof T : iProp_to_Prop (typed_annot_stmt a l P T).

  Definition typed_if (ot : op_type) (v : val) (ty : type) `{!Movable ty} (T1 T2 : iProp Σ) : iProp Σ :=
    (* TODO: generalize this to PtrOp *)
    (v ◁ᵥ ty -∗ ∃ it z, ⌜ot = IntOp it⌝ ∗ ⌜val_to_int v it = Some z⌝ ∗ (if decide (z = 0) then T2 else T1)).
  Class TypedIf (ot : op_type) (v : val) (ty : type) `{!Movable ty} : Type :=
    typed_if_proof T1 T2 : iProp_to_Prop (typed_if ot v ty T1 T2).

  (*** statements *)
  Record fn_ret := FR {
    fr_rty : mtype;
    fr_R : iProp Σ;
  }.
  Definition mk_FR (rty : type) `{!Movable rty} (R : iProp Σ) := FR (t2mt rty) R.

  Definition typed_stmt_post_cond {B} (fn : function) (ls : list loc) (fr : B → fn_ret) (v : val) : iProp Σ :=
    (∃ x, v ◁ᵥ (fr x).(fr_rty) ∗ ([∗ list] l;v ∈ ls;(fn.(f_args) ++ fn.(f_local_vars)), l ↦|v.2|) ∗ (fr x).(fr_R))%I.
  Definition typed_stmt {B} (s : stmt) (fn : function) (ls : list loc) (fr : B → fn_ret) (Q : gmap label stmt) : iProp Σ :=
    (⌜length ls = length (fn.(f_args) ++ fn.(f_local_vars))⌝ -∗ WPs s {{Q, typed_stmt_post_cond fn ls fr}})%I.
  Global Arguments typed_stmt {_} _%E _ _ _%I _.

  Definition typed_block {B} (P : iProp Σ) (b : label) (fn : function) (ls : list loc) (fr : B → fn_ret) (Q : gmap label stmt) : iProp Σ :=
    (wps_block P b Q (typed_stmt_post_cond fn ls fr)).

  Definition typed_switch {B} (v : val) (ty : type) `{!Movable ty} (it : int_type) (m : gmap Z nat) (ss : list stmt) (def : stmt) (fn : function) (ls : list loc) (fr : B → fn_ret) (Q : gmap label stmt) : iProp Σ :=
    (v ◁ᵥ ty -∗ ∃ z, ⌜val_to_int v it = Some z⌝ ∗
      match m !! z with
      | Some i => ∃ s, ⌜ss !! i = Some s⌝ ∗ typed_stmt s fn ls fr Q
      | None   => typed_stmt def fn ls fr Q
      end).
  Class TypedSwitch (v : val) (ty : type) `{!Movable ty} (it : int_type) : Type :=
    typed_switch_proof B m ss def fn ls fr Q : iProp_to_Prop (typed_switch (B:=B) v ty it m ss def fn ls fr Q).

  Definition typed_assert {B} (v : val) (ty : type) `{!Movable ty} (s : stmt) (fn : function) (ls : list loc) (fr : B → fn_ret) (Q : gmap label stmt) : iProp Σ :=
    (v ◁ᵥ ty -∗ ∃ z, ⌜val_to_int v bool_it = Some z⌝ ∗ ⌜z ≠ 0⌝ ∗ typed_stmt s fn ls fr Q)%I.
  Class TypedAssert (v : val) (ty : type) `{!Movable ty} : Type :=
    typed_assert_proof B s fn ls fr Q : iProp_to_Prop (typed_assert (B:=B) v ty s fn ls fr Q).
  (*** expressions *)
  Definition typed_val_expr (e : expr) (T : val → mtype → iProp Σ) : iProp Σ :=
    (∀ Φ, (∀ v (ty : mtype), v ◁ᵥ ty -∗ T v ty -∗ Φ v) -∗ WP e {{ Φ }}).
  Global Arguments typed_val_expr _%E _%I.

  Definition typed_value (v : val) (T : mtype → iProp Σ) : iProp Σ :=
    (∃ (ty: mtype), v ◁ᵥ ty ∗ T ty).
  Class TypedValue (v : val) : Type :=
    typed_value_proof T : iProp_to_Prop (typed_value v T).

  Definition typed_bin_op (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (o : bin_op) (ot1 ot2 : op_type) (T : val → mtype → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr (BinOp o ot1 ot2 v1 v2) T).

  Class TypedBinOp (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_proof T : iProp_to_Prop (typed_bin_op v1 P1 v2 P2 o ot1 ot2 T).
  Class TypedBinOpVal (v1 : val) (ty1 : type) `{!Movable ty1} (v2 : val) (ty2 : type) `{!Movable ty2} (o : bin_op) (ot1 ot2 : op_type) : Type :=
    typed_bin_op_val :> TypedBinOp v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) o ot1 ot2.

  Definition typed_un_op (v : val) (P : iProp Σ) (o : un_op) (ot : op_type) (T : val → mtype → iProp Σ) : iProp Σ :=
    (P -∗ typed_val_expr (UnOp o ot v) T).

  Class TypedUnOp (v : val) (P : iProp Σ) (o : un_op) (ot : op_type) : Type :=
    typed_un_op_proof T : iProp_to_Prop (typed_un_op v P o ot T).
  Class TypedUnOpVal (v : val) (ty : type) `{!Movable ty} (o : un_op) (ot : op_type) : Type :=
    typed_un_op_val :> TypedUnOp v (v ◁ᵥ ty) o ot.

  Definition typed_copy_alloc_id (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (T : val → mtype → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ typed_val_expr (CopyAllocId v1 v2) T).

  Class TypedCopyAllocId (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) : Type :=
    typed_copy_alloc_id_proof T : iProp_to_Prop (typed_copy_alloc_id v1 P1 v2 P2 T).
  Class TypedCopyAllocIdVal (v1 : val) (ty1 : type) `{!Movable ty1} (v2 : val) (ty2 : type) `{!Movable ty2} : Type :=
    typed_copy_alloc_id_val :> TypedCopyAllocId v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2).

  Definition typed_cas (ot : op_type) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ)  (T : val → mtype → iProp Σ) : iProp Σ :=
    (P1 -∗ P2 -∗ P3 -∗ typed_val_expr (CAS ot v1 v2 v3) T).
  Class TypedCas (ot : op_type) (v1 : val) (P1 : iProp Σ) (v2 : val) (P2 : iProp Σ) (v3 : val) (P3 : iProp Σ) : Type :=
    typed_cas_proof T : iProp_to_Prop (typed_cas ot v1 P1 v2 P2 v3 P3 T).

  (* This does not allow overloading the macro based on the type of
  es. Is this a problem? There is a work around where the rule inserts
  another judgment that allows type-based overloading. *)
  Definition typed_macro_expr (m : list expr → expr) (es : list expr) (T : val → mtype → iProp Σ) : iProp Σ :=
    (typed_val_expr (m es) T).
  Class TypedMacroExpr (m : list expr → expr) (es : list expr) : Type :=
    typed_macro_expr_proof T : iProp_to_Prop (typed_macro_expr m es T).

  (*** places *)
  Definition typed_write (atomic : bool) (e : expr) (v : val) (ty : type) `{!Movable ty} (T : iProp Σ) : iProp Σ :=
    let E := if atomic then ∅ else ⊤ in
    (∀ Φ,
       (∀ (l : loc), (v ◁ᵥ ty ={⊤, E}=∗ l↦|ty.(ty_layout)| ∗ ▷ (l ↦ v ={E, ⊤}=∗ T)) -∗ Φ (val_of_loc l)) -∗
       WP e {{ Φ }}).

  Definition typed_read (atomic : bool) (e : expr) (ly : layout) (T : val → mtype → iProp Σ) : iProp Σ :=
    let E := if atomic then ∅ else ⊤ in
    (∀ Φ,
       (∀ (l : loc), (|={⊤, E}=> ∃ v q (ty : mtype), ⌜l `has_layout_loc` ly⌝ ∗ ⌜v `has_layout_val` ly⌝ ∗ l↦{q}v ∗ ▷ v ◁ᵥ ty ∗ ▷ (l↦{q}v ={E, ⊤}=∗ T v ty)) -∗ Φ (val_of_loc l)) -∗
       WP e {{ Φ }}).

  Definition typed_addr_of (e : expr) (T : loc → own_state → type → iProp Σ) : iProp Σ :=
    (∀ Φ,
       (∀ (l : loc) β ty, l ◁ₗ{β} ty -∗ T l β ty -∗ Φ (val_of_loc l)) -∗
       WP e {{ Φ }}).

  Definition typed_read_end (atomic : bool) (l : loc) (β : own_state) (ty : type) (ly : layout) (T : val → type → mtype → iProp Σ) : iProp Σ :=
    let E := if atomic then ∅ else ⊤ in
    l◁ₗ{β}ty ={⊤, E}=∗ ∃ q v ty' (ty2 : mtype),
        ⌜l `has_layout_loc` ly⌝ ∗ ⌜v `has_layout_val` ly⌝ ∗ l↦{q}v ∗ ▷ v ◁ᵥ ty2 ∗ ▷ (l↦{q}v ={E, ⊤}=∗ l◁ₗ{β} ty' ∗ T v ty' ty2).
  Class TypedReadEnd (atomic : bool) (l : loc) (β : own_state) (ty : type) (ly : layout) : Type :=
    typed_read_end_proof T : iProp_to_Prop (typed_read_end atomic l β ty ly T).

  Definition typed_write_end (atomic : bool) (v1 : val) (ty1 : type) `{!Movable ty1} (l2 : loc) (β2 : own_state) (ty2 : type) (T : type → iProp Σ) : iProp Σ :=
    let E := if atomic then ∅ else ⊤ in
    l2 ◁ₗ{β2} ty2 -∗ v1 ◁ᵥ ty1 ={⊤, E}=∗ l2↦|ty1.(ty_layout)| ∗ ▷ (l2↦v1 ={E, ⊤}=∗ ∃ ty3, l2 ◁ₗ{β2} ty3 ∗ T ty3).
  Class TypedWriteEnd (atomic : bool) (v1 : val) (ty1 : type) `{!Movable ty1} (l2 : loc) (β2 : own_state) (ty2 : type) : Type :=
    typed_write_end_proof T : iProp_to_Prop (typed_write_end atomic v1 ty1 l2 β2 ty2 T).

  Definition typed_addr_of_end (l : loc) (β : own_state) (ty : type) (T : own_state → type → type → iProp Σ) : iProp Σ :=
    l◁ₗ{β}ty ={⊤}=∗ ∃ β2 ty2 ty', l◁ₗ{β2}ty2 ∗ l◁ₗ{β}ty' ∗ T β2 ty2 ty'.
  Class TypedAddrOfEnd (l : loc) (β : own_state) (ty : type) : Type :=
    typed_addr_of_end_proof T : iProp_to_Prop (typed_addr_of_end l β ty T).

  (*** typed places *)
  (* This defines what place expressions can contain. We cannot reuse
  W.ectx_item because of BinOpPCtx since there the root of the place
  expression is not in evaluation position. *)
  (* TODO: Should we track location information here? *)
  Inductive place_ectx_item :=
  | DerefPCtx (o : order) (l : layout)
  | GetMemberPCtx (s : struct_layout) (m : var_name)
  | GetMemberUnionPCtx (ul : union_layout) (m : var_name)
  | AnnotExprPCtx (n : nat) {A} (x : A)
    (* for PtrOffsetOp, second ot must be PtrOp *)
  | BinOpPCtx (op : bin_op) (ot : op_type) (v : val) (ty : mtype)
    (* for ptr-to-ptr casts, ot must be PtrOp *)
  | UnOpPCtx (op : un_op)
  .

  (* Computes the WP one has to prove for the place ectx_item Ki
  applied to the location l. *)
  Definition place_item_to_wp (Ki : place_ectx_item) (Φ : loc → iProp Σ) (l : loc) : iProp Σ :=
    match Ki with
    | DerefPCtx o ly => WP !{ly, o} l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberPCtx sl m => WP l at{sl} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | GetMemberUnionPCtx ul m => WP l at_union{ul} m {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | AnnotExprPCtx n x => WP AnnotExpr n x l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    (* we have proved typed_val_expr e1 before so we can use v ◁ᵥ ty here *)
    | BinOpPCtx op ot v ty => v ◁ᵥ ty -∗ WP BinOp op ot PtrOp v l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    | UnOpPCtx op => WP UnOp op PtrOp l {{ v, ∃ l' : loc, ⌜v = val_of_loc l'⌝ ∗ Φ l' }}
    end%I.
  Definition place_to_wp (K : list place_ectx_item) (Φ : loc → iProp Σ) : (loc → iProp Σ) := foldr place_item_to_wp Φ K.
  Lemma place_to_wp_app (K1 K2 : list place_ectx_item) Φ : place_to_wp (K1 ++ K2) Φ = place_to_wp K1 (place_to_wp K2 Φ).
  Proof. apply foldr_app. Qed.

  Lemma place_item_to_wp_mono K Φ1 Φ2 l:
    place_item_to_wp K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_item_to_wp K Φ2 l.
  Proof.
    iIntros "HP HΦ". move: K => [o ly|sl m|ul m|n A x|op ot v ty|op]//=.
    5: iIntros "Hv".
    1-4,6: iApply (@wp_wand with "HP").
    6: iApply (@wp_wand with "[Hv HP]"); first by iApply "HP".
    all: iIntros (?); iDestruct 1 as (l' ->) "HΦ1".
    all: iExists _; iSplit => //; by iApply "HΦ".
  Qed.

  Lemma place_to_wp_mono K Φ1 Φ2 l:
    place_to_wp K Φ1 l -∗ (∀ l, Φ1 l -∗ Φ2 l) -∗ place_to_wp K Φ2 l.
  Proof.
    iIntros "HP HΦ".
    iInduction (K) as [] "IH" forall (l) => /=. by iApply "HΦ".
    iApply (place_item_to_wp_mono with "HP").
    iIntros (l') "HP". by iApply ("IH" with "HP HΦ").
  Qed.

  Fixpoint find_place_ctx (e : W.expr) : option ((list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    match e with
    | W.Loc l => Some (λ T, T [] l)
    | W.Deref o ly e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [DerefPCtx o ly]) l))
    | W.GetMember e sl m => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [GetMemberPCtx sl m]) l))
    | W.GetMemberUnion e ul m => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [GetMemberUnionPCtx ul m]) l))
    | W.AnnotExpr n x e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [AnnotExprPCtx n x]) l))
    | W.LocInfoE a e => find_place_ctx e
    (* Here we use the power of having a continuation available to add
    a typed_val_expr. It is important that this happens before we get
    to place_to_wp_mono since we will need to give up ownership of the
    root of the place expression once we hit it. This allows us to
    support e.g. a[a[0]]. *)
    | W.BinOp op ot PtrOp e1 e2 => T' ← find_place_ctx e2; Some (λ T, typed_val_expr (W.to_expr e1) (λ v ty, T' (λ K l, T (K ++ [BinOpPCtx op ot v ty]) l)))
    | W.UnOp op PtrOp e => T' ← find_place_ctx e; Some (λ T, T' (λ K l, T (K ++ [UnOpPCtx op]) l))
    (* TODO: Is the existential quantifier here a good idea or should this be a fullblown judgment? *)
    | W.LValue e => Some (λ T, typed_val_expr (W.to_expr e) (λ v ty, v ◁ᵥ ty -∗ ∃ l, ⌜v = val_of_loc l⌝ ∗ T [] l)%I)
    | _ => None
    end.

  Class IntoPlaceCtx (e : expr) (T : (list place_ectx_item → loc → iProp Σ) → iProp Σ) :=
    into_place_ctx Φ Φ': (⊢ T Φ' -∗ (∀ K l, Φ' K l -∗ place_to_wp K (Φ ∘ val_of_loc) l) -∗ WP e {{ Φ }}).

  Section find_place_ctx_correct.
  Arguments W.to_expr : simpl nomatch.
  Lemma find_place_ctx_correct e T:
    find_place_ctx e = Some T →
    IntoPlaceCtx (W.to_expr e) T.
  Proof.
    elim: e T => //= *.
    all: iIntros (Φ Φ') "HT HΦ'".
    2,3: case_match.
    all: try match goal with
    |  H : ?x ≫= _ = Some _ |- _ => destruct x as [?|] eqn:Hsome
    end; simplify_eq/=.
    all: try match goal with
    |  H : context [IntoPlaceCtx _ _] |- _ => rename H into IH
    end.
    1: iApply @wp_value; by iApply ("HΦ'" with "HT").
    4: {
      rewrite /LValue. iApply "HT". iIntros (v ty) "Hv HT".
      iDestruct ("HT" with "Hv") as (l ?) "HT". subst.
      by iApply ("HΦ'" $! []).
    }
    2: wp_bind; rewrite -!/(W.to_expr _).
    2: iApply "HT"; iIntros (v ty) "Hv HT".
    2: iDestruct (IH with "HT") as "HT" => //.
    1, 3-6: iDestruct (IH with "HT") as " HT" => //.
    all: wp_bind; iApply "HT".
    all: iIntros (K l) "HT" => /=.
    all: iDestruct ("HΦ'" with "HT") as "HΦ"; rewrite place_to_wp_app /=.
    all: iApply (place_to_wp_mono with "HΦ"); iIntros (l') "HWP" => /=.
    6: iApply (@wp_wand with "[Hv HWP]"); first by iApply "HWP".
    1-5: iApply (@wp_wand with "HWP").
    all: iIntros (?); by iDestruct 1 as (? ->) "$".
  Qed.
  End find_place_ctx_correct.

  (* TODO: have something like typed_place_cond which uses a fraction? Seems *)
  (* tricky since stating that they have the same size requires that ty1 *)
  (* and ty2 are movable (which they might not be) *)
  Definition typed_place (P : list place_ectx_item) (l1 : loc) (β1 : own_state) (ty1 : type) (T : loc → own_state → type → (type → type) → (type → iProp Σ) → iProp Σ) : iProp Σ :=
    (∀ Φ, l1 ◁ₗ{β1} ty1 -∗
       (∀ (l2 : loc) β2 ty2 typ R, l2 ◁ₗ{β2} ty2 -∗ (∀ ty', l2 ◁ₗ{β2} ty' ={⊤}=∗ l1 ◁ₗ{β1} typ ty' ∗ R ty') -∗ T l2 β2 ty2 typ R -∗ Φ l2) -∗ place_to_wp P Φ l1).
  Class TypedPlace (P : list place_ectx_item) (l1 : loc) (β1 : own_state) (ty1 : type) : Type :=
    typed_place_proof T : iProp_to_Prop (typed_place P l1 β1 ty1 T).

End judgements.

Ltac solve_into_place_ctx :=
  match goal with
  | |- IntoPlaceCtx ?e ?T =>
      let e' := W.of_expr e in
      change_no_check (IntoPlaceCtx (W.to_expr e') T);
      refine (find_place_ctx_correct _ _ _); rewrite/=/W.to_expr/=; done
  end.
Hint Extern 0 (IntoPlaceCtx _ _) => solve_into_place_ctx : typeclass_instances.

Hint Mode SimplifyHypPlace + + + + + - : typeclass_instances.
Hint Mode SimplifyHypVal + + + + + - : typeclass_instances.
Hint Mode SimplifyGoalPlace + + + + ! - : typeclass_instances.
Hint Mode SimplifyGoalVal + + + ! ! - : typeclass_instances.
Hint Mode CopyAs + + + + + : typeclass_instances.
Hint Mode SubsumePlace + + + + + ! : typeclass_instances.
Hint Mode SubsumeVal + + + + ! + ! : typeclass_instances.
Hint Mode SimpleSubsumePlace + + + ! - : typeclass_instances.
Hint Mode SimpleSubsumePlaceR + + + ! + ! - : typeclass_instances.
Hint Mode SimpleSubsumeVal + + + ! + ! - : typeclass_instances.
Hint Mode TypedIf + + + + + + : typeclass_instances.
Hint Mode TypedAssert + + + + + : typeclass_instances.
Hint Mode TypedValue + + + : typeclass_instances.
Hint Mode TypedBinOp + + + + + + + + + : typeclass_instances.
Hint Mode TypedBinOpVal + + + + + + + + + + + : typeclass_instances.
Hint Mode TypedUnOp + + + + + + : typeclass_instances.
Hint Mode TypedUnOpVal + + + + + + + : typeclass_instances.
Hint Mode TypedCopyAllocId + + + + + + : typeclass_instances.
Hint Mode TypedCopyAllocIdVal + + + + + + + + : typeclass_instances.
Hint Mode TypedReadEnd + + + + + + + : typeclass_instances.
Hint Mode TypedWriteEnd + + + + + + + + + : typeclass_instances.
Hint Mode TypedAddrOfEnd + + + + + : typeclass_instances.
Hint Mode TypedPlace + + + + + + : typeclass_instances.
Hint Mode TypedAnnotExpr + + + + + + + : typeclass_instances.
Hint Mode TypedAnnotStmt + + + + + + : typeclass_instances.
Hint Mode TypedMacroExpr + + + + : typeclass_instances.
Arguments typed_annot_expr : simpl never.
Arguments typed_annot_stmt : simpl never.
Arguments typed_macro_expr : simpl never.
Arguments learnalign_align {_ _ _ _} _.
Arguments learnalign_learn {_ _ _ _} _.

Section proper.
  Context `{!typeG Σ}.

  Lemma simplify_hyp_place_eq l β ty1 ty2 T:
    ty1 ≡@{type} ty2 →
    (l ◁ₗ{β} ty2 -∗ T) -∗ simplify_hyp (l◁ₗ{β} ty1) T.
  Proof. iIntros (->) "HT ?". by iApply "HT". Qed.

  Lemma simplify_goal_place_eq l β ty1 ty2 T:
    ty1 ≡@{type} ty2 →
    T (l ◁ₗ{β} ty2) -∗ simplify_goal (l◁ₗ{β} ty1) T.
  Proof. iIntros (Heq) "HT". iExists _. iFrame. rewrite Heq. by iIntros "?". Qed.

  Lemma simplify_hyp_val_eq v ty1 ty2 (Heq : ty1 ≡ ty2) {Hm: Movable ty1} `{!Movable ty2} T:
    Hm = movable_eq ty1 ty2 Heq →
    (v ◁ᵥ ty2 -∗ T) -∗ simplify_hyp (v ◁ᵥ ty1) T.
  Proof. by move => ->. Qed.

  Lemma simplify_goal_val_eq v ty1 ty2 (Heq : ty1 ≡ ty2) {Hm: Movable ty1} `{!Movable ty2} T:
    Hm = movable_eq ty1 ty2 Heq →
    T (v ◁ᵥ ty2) -∗ simplify_goal (v ◁ᵥ ty1) T.
  Proof. iIntros (->) "HT". iExists _. iFrame. by iIntros "?". Qed.

  (* TODO: this lemma is not very useful. figure out how to make it useful *)
  Lemma typed_place_mono P l ty1 ty2 β T1 T2 :
    typed_place P l β ty2 T1 -∗ (l ◁ₗ{β} ty1 -∗ l ◁ₗ{β} ty2) -∗ (∀ l2 β2 ty3 typ R, T1 l2 β2 ty3 typ R -∗ T2 l2 β2 ty3 typ R) -∗ typed_place P l β ty1 T2.
  Proof.
    iIntros "HP Hlsub HTsub" (Φ) "Hl HΦ". iApply ("HP" with "[Hl Hlsub]"). by iApply "Hlsub".
    iIntros (l' ty3 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' Htyp"). by iApply "HTsub".
  Qed.

  Lemma typed_place_subsume' P l ty1 β T :
    (l ◁ₗ{β} ty1 -∗ ∃ ty2, l ◁ₗ{β} ty2 ∗ typed_place P l β ty2 T) -∗ typed_place P l β ty1 T.
  Proof.
    iIntros "Hsub" (Φ) "Hl HΦ". iDestruct ("Hsub" with "Hl") as (ty2) "[Hl HP]". by iApply ("HP" with "Hl").
  Qed.

  Lemma typed_place_subsume P l ty1 ty2 β T :
    subsume (l ◁ₗ{β} ty1) (l ◁ₗ{β} ty2) (typed_place P l β ty2 T) -∗ typed_place P l β ty1 T.
  Proof.
    iIntros "Hsub". iApply typed_place_subsume'. iIntros "Hl". iExists _. by iApply "Hsub".
  Qed.
End proper.

Definition FindLoc `{!typeG Σ} (l : loc) :=
  {| fic_A := own_state * type; fic_Prop '(β, ty):= (l ◁ₗ{β} ty)%I; |}.
Definition FindVal `{!typeG Σ} (v : val) :=
  {| fic_A := mtype; fic_Prop ty := (v ◁ᵥ ty)%I; |}.
Definition FindValP {Σ} (v : val) :=
  {| fic_A := iProp Σ; fic_Prop P := P; |}.
Definition FindLocInBounds {Σ} (l : loc) :=
    {| fic_A := iProp Σ; fic_Prop P := P |}.
Typeclasses Opaque FindLoc FindVal FindValP FindLocInBounds.

Section typing.
  Context `{!typeG Σ}.

  Lemma find_in_context_type_loc_id l T:
    (∃ β ty, l ◁ₗ{β} ty ∗ T (β, ty)) -∗
    find_in_context (FindLoc l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists (_, _) => /=. iFrame. Qed.
  Global Instance find_in_context_type_loc_id_inst l :
    FindInContext (FindLoc l) 0%nat :=
    λ T, i2p (find_in_context_type_loc_id l T).

  Lemma find_in_context_type_val_id v T:
    (∃ ty : mtype, v ◁ᵥ ty ∗ T ty) -∗
    find_in_context (FindVal v) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_id_inst v :
    FindInContext (FindVal v) 0%nat :=
    λ T, i2p (find_in_context_type_val_id v T).

  Lemma find_in_context_type_val_P_id v T:
    (∃ ty : mtype, v ◁ᵥ ty ∗ T (v ◁ᵥ ty)) -∗
    find_in_context (FindValP v) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists (ty_own_val _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_P_id_inst v :
    FindInContext (FindValP v) 0%nat :=
    λ T, i2p (find_in_context_type_val_P_id v T).

  Lemma find_in_context_type_val_P_loc_id l T:
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty)) -∗
    find_in_context (FindValP l) T.
  Proof. iDestruct 1 as (β ty) "[Hl HT]". iExists (ty_own _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_type_val_P_loc_id_inst (l : loc) :
    FindInContext (FindValP l) 1%nat :=
    λ T, i2p (find_in_context_type_val_P_loc_id l T).

  Lemma find_in_context_loc_in_bounds l T :
    (∃ n, loc_in_bounds l n ∗ T (loc_in_bounds l n)) -∗
    find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (n) "[??]". iExists (loc_in_bounds _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_inst l :
    FindInContext (FindLocInBounds l) 0 :=
    λ T, i2p (find_in_context_loc_in_bounds l T).

  Lemma find_in_context_loc_in_bounds_loc l T :
    (∃ β ty, l ◁ₗ{β} ty ∗ T (l ◁ₗ{β} ty)) -∗
    find_in_context (FindLocInBounds l) T.
  Proof. iDestruct 1 as (β ty) "[??]". iExists (ty_own _ _ _) => /=. iFrame. Qed.
  Global Instance find_in_context_loc_in_bounds_loc_inst l :
    FindInContext (FindLocInBounds l) 1 :=
    λ T, i2p (find_in_context_loc_in_bounds_loc l T).

  Global Instance related_to_loc l β ty : RelatedTo (l ◁ₗ{β} ty) := {| rt_fic := FindLoc l |}.
  Global Instance related_to_val v ty `{!Movable ty} : RelatedTo (v ◁ᵥ ty) := {| rt_fic := FindValP v |}.
  Global Instance related_to_loc_in_bounds l n : RelatedTo (loc_in_bounds l n) := {| rt_fic := FindLocInBounds l |}.
  Global Instance related_to_alloc_alive l : RelatedTo (alloc_alive l.1) := {| rt_fic := FindLoc l |}.

  Lemma subsume_loc_in_bounds ty β l (n m : nat) `{!LocInBounds ty β m} T :
    (l ◁ₗ{β} ty -∗ ⌜n ≤ m⌝ ∗ T) -∗
    subsume (l ◁ₗ{β} ty) (loc_in_bounds l n) T.
  Proof.
    iIntros "HT Hl".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#?".
    iDestruct ("HT" with "Hl") as (?) "$".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.
  Global Instance subsume_loc_in_bounds_inst ty β l n m `{!LocInBounds ty β m} :
    Subsume (l ◁ₗ{β} ty) (loc_in_bounds l n) :=
    λ T, i2p (subsume_loc_in_bounds ty β l n m T).

  Lemma subsume_alloc_alive ty β l P `{!AllocAlive ty β P} T :
    (* You don't get l ◁ₗ{β} ty back because alloc_alive is not persistent. *)
    P ∗ T -∗
    subsume (l ◁ₗ{β} ty) (alloc_alive l.1) T.
  Proof. iIntros "[HP $] Hl". by iApply (alloc_alive_alive with "HP"). Qed.
  Global Instance subsume_alloc_alive_inst ty β l P `{!AllocAlive ty β P} :
    Subsume (l ◁ₗ{β} ty) (alloc_alive l.1) :=
    λ T, i2p (subsume_alloc_alive ty β l P T).

  Lemma subsume_loc_in_bounds_leq (l : loc) (n1 n2 : nat) T :
    ⌜n2 ≤ n1⌝%nat ∗ T -∗
    subsume (loc_in_bounds l n1) (loc_in_bounds l n2) T.
  Proof. iIntros "[% $] #?". by iApply loc_in_bounds_shorten. Qed.
  Global Instance subsume_loc_in_bounds_leq_inst (l : loc) (n1 n2 : nat):
    Subsume (loc_in_bounds l n1) (loc_in_bounds l n2) :=
    λ T, i2p (subsume_loc_in_bounds_leq l n1 n2 T).

  Lemma apply_subsume_place_true l1 β1 ty1 l2 β2 ty2:
    l1 ◁ₗ{β1} ty1 -∗
    subsume (l1 ◁ₗ{β1} ty1) (l2 ◁ₗ{β2} ty2) True -∗
    l2 ◁ₗ{β2} ty2.
  Proof. iIntros "Hl1 Hsub". iDestruct ("Hsub" with "Hl1") as "[$ _]". Qed.

  Lemma apply_subsume_place l ty2 T:
    (find_in_context (FindDirect (λ '(β, ty), l◁ₗ{β}ty)) (λ '(β, ty), subsume (l◁ₗ{β} ty) (l◁ₗ{β} ty2) (l◁ₗ{β}ty2 -∗ T))) -∗ T.
  Proof.
    iDestruct 1 as ([β ty1]) "[Hl Hsub]". iDestruct ("Hsub" with "Hl") as "[Hl HT]". by iApply "HT".
  Qed.

  Lemma simplify_place_refine_l (ty : rtype) l β T:
    (∀ x, l◁ₗ{β} x@ty -∗ T) -∗ simplify_hyp (l◁ₗ{β}ty) T.
  Proof.
    iIntros "HT Hl". iDestruct "Hl" as (x) "Hv". by iApply "HT".
  Qed.
  Global Instance simplify_place_refine_l_inst (ty : rtype) l β:
    SimplifyHypPlace l β ty (Some 0%N) :=
    λ T, i2p (simplify_place_refine_l ty l β T).

  Lemma simplify_val_refine_l (ty : rtype) v T `{!RMovable ty} `{!Inhabited (ty.(rty_type))}:
    (∀ x, v◁ᵥ (x @ ty) -∗ T) -∗ simplify_hyp (v◁ᵥty) T.
  Proof.
    iIntros "HT Hl". iDestruct "Hl" as (x) "Hv". by iApply "HT".
  Qed.
  Global Instance simplify_val_refine_l_inst (ty : rtype) v `{!RMovable ty} `{!Inhabited (ty.(rty_type))}:
    SimplifyHypVal v ty (Some 0%N) :=
    λ T, i2p (simplify_val_refine_l ty v T).

  (* This is forced since it can create evars in places where we don't
  want them. We might first want to try subtyping without the evar (see e.g. optional ) *)
  Lemma simplify_goal_place_refine_r (ty : rtype) l β T:
    (∃ x, T (l ◁ₗ{β} (x @ ty))) -∗ simplify_goal (l◁ₗ{β}ty) T.
  Proof. iDestruct 1 as (x) "HT". iExists _. iFrame. iIntros "?". by iExists _. Qed.
  Global Instance simplfy_goal_place_refine_r_inst (ty : rtype) l β :
    SimplifyGoalPlace l β ty (Some 10%N) :=
    λ T, i2p (simplify_goal_place_refine_r ty l β T).

  Lemma simplify_goal_val_refine_r (ty : rtype) v T  `{!RMovable ty} `{!Inhabited (ty.(rty_type))} :
    (∃ x, T (v ◁ᵥ (x @ ty))) -∗ simplify_goal (v◁ᵥty) T.
  Proof. iDestruct 1 as (x) "HT". iExists _. iFrame. iIntros "?". by iExists _. Qed.
  Global Instance simplfy_goal_val_refine_r_inst (ty : rtype) v `{!RMovable ty} `{!Inhabited (ty.(rty_type))} :
    SimplifyGoalVal v ty (Some 10%N) :=
    λ T, i2p (simplify_goal_val_refine_r ty v T).

  (* The match can come from own_state_min *)
  Lemma simplify_bad_own_state_hyp l β ty T:
    (l ◁ₗ{β} ty -∗ T) -∗
    simplify_hyp (l ◁ₗ{match β with | Own => Own | Shr => Shr end} ty) T.
  Proof. by destruct β. Qed.
  Global Instance simplify_bad_own_state_hyp_inst l β ty :
    SimplifyHypPlace l (match β with | Own => Own | Shr => Shr end) ty (Some 0%N) :=
    λ T, i2p (simplify_bad_own_state_hyp l β ty T).

  Lemma simplify_bad_own_state_goal l β ty T:
    (T (l ◁ₗ{β} ty)) -∗
    simplify_goal (l ◁ₗ{match β with | Own => Own | Shr => Shr end} ty) T.
  Proof. iIntros "HT". iExists _. iFrame. iIntros "?". by destruct β. Qed.
  Global Instance simplify_bad_own_state_goal_inst l β ty :
    SimplifyGoalPlace l (match β with | Own => Own | Shr => Shr end) ty (Some 0%N) :=
    λ T, i2p (simplify_bad_own_state_goal l β ty T).

  (* TODO: generalize this to more simplifications? *)
  Lemma simplify_hyp_place_Z_to_nat ly l β ty n T:
    ⌜0 ≤ n⌝ ∗ ((l offset{ly}ₗ n) ◁ₗ{β} ty -∗ T) -∗ simplify_hyp ((l offset{ly}ₗ Z.to_nat n) ◁ₗ{β} ty) T.
  Proof. iIntros "[% HT]". rewrite Z2Nat.id //. Qed.
  Global Instance simplify_hyp_place_Z_to_nat_inst ly l β ty n:
    SimplifyHypPlace (l offset{ly}ₗ Z.to_nat n) β ty (Some 0%N) :=
    λ T, i2p (simplify_hyp_place_Z_to_nat ly l β ty n T).

  Lemma simplify_goal_place_Z_to_nat ly l β ty n T:
    ⌜0 ≤ n⌝ ∗ T ((l offset{ly}ₗ n) ◁ₗ{β} ty) -∗ simplify_goal ((l offset{ly}ₗ Z.to_nat n) ◁ₗ{β} ty) T.
  Proof. iIntros "[% HT]". rewrite Z2Nat.id //. iExists _. iFrame. iIntros "$". Qed.
  Global Instance simplify_goal_place_Z_to_nat_inst ly l β ty n:
    SimplifyGoalPlace (l offset{ly}ₗ Z.to_nat n) β ty (Some 0%N) :=
    λ T, i2p (simplify_goal_place_Z_to_nat ly l β ty n T).

  Global Instance simple_subsume_place_id ty : SimpleSubsumePlace ty ty True | 1.
  Proof. iIntros (??) "_ $". Qed.
  Global Instance simple_subsume_place_r_id ty x : SimpleSubsumePlaceR ty ty x x True | 1.
  Proof. iIntros (??) "_ $". Qed.
  Global Instance simple_subsume_val_id ty `{!Movable ty} : SimpleSubsumeVal ty ty True | 1.
  Proof. iIntros (?) "_ $". Qed.
  Global Instance simple_subsume_val_refinement_id ty x1 x2 `{!RMovable ty} :
    SimpleSubsumeVal (x1 @ ty) (x2 @ ty) (⌜x1 = x2⌝) | 100.
  Proof. iIntros (? ->) "$". Qed.

  Lemma simple_subsume_place_to_subsume l β ty1 ty2 P `{!SimpleSubsumePlace ty1 ty2 P} T:
    P ∗ T -∗ subsume (l ◁ₗ{β} ty1) (l ◁ₗ{β} ty2) T.
  Proof. iIntros "[HP $] Hl". iApply (@simple_subsume_place with "HP Hl"). Qed.
  Global Instance simple_subsume_place_to_subsume_inst l β ty1 ty2 P `{!SimpleSubsumePlace ty1 ty2 P}:
    SubsumePlace l β ty1 ty2 := λ T, i2p (simple_subsume_place_to_subsume l β ty1 ty2 P T).

  Lemma simple_subsume_val_to_subsume v ty1 ty2 P `{!Movable ty1} `{!Movable ty2} `{!SimpleSubsumeVal ty1 ty2 P} T:
    P ∗ T -∗ subsume (v ◁ᵥ ty1) (v ◁ᵥ ty2) T.
  Proof. iIntros "[HP $] Hv". iApply (@simple_subsume_val with "HP Hv"). Qed.
  Global Instance simple_subsume_val_to_subsume_inst v ty1 ty2 P `{!Movable ty1} `{!Movable ty2} `{!SimpleSubsumeVal ty1 ty2 P}:
    SubsumeVal v ty1 ty2 := λ T, i2p (simple_subsume_val_to_subsume v ty1 ty2 P T).

  Import EqNotations.
  Lemma simple_subsume_place_refinement ty1 ty2 (x1 : ty1.(rty_type)) x2 P {Heq: ty1.(rty_type) = ty2.(rty_type)} `{!SimpleSubsumePlaceR ty1 ty2 x1 (rew [λ x : Type, x] Heq in x1) P} :
    SimpleSubsumePlace (x1 @ ty1) (x2 @ ty2) (⌜rew [λ x : Type, x] Heq in x1 = x2⌝ ∗ P).
  Proof.
    iIntros (l β) "HP Hl". iDestruct "HP" as (Heq2) "HP".
    iDestruct (@simple_subsume_place_r with "HP Hl") as "Hl" => //.
      by rewrite Heq2.
  Qed.

  Lemma simple_subsume_place_refinement_eq ty1 ty2 (x1 : ty1.(rty_type)) x2 P (Heq: ty1.(rty_type) = ty2.(rty_type)) (Heq2 : rew [λ x : Type, x] Heq in x1 = x2 ) `{!SimpleSubsumePlaceR ty1 ty2 x1 (rew [λ x : Type, x] Heq in x1) P} :
    SimpleSubsumePlace (x1 @ ty1) (x2 @ ty2) P.
  Proof. iIntros (l β) "HP Hl". iDestruct (@simple_subsume_place_r with "HP Hl") as "Hl" => //. by rewrite Heq2. Qed.

  Global Instance simple_subsume_place_rty_to_ty_l (ty1 : rtype) P `{!∀ x, SimpleSubsumePlace (x @ ty1) ty2 P} :
    SimpleSubsumePlace ty1 ty2 P.
  Proof.
    iIntros (l β) "HP Hl". iDestruct "Hl" as (x) "Hl".
    iApply (@simple_subsume_place with "HP Hl").
  Qed.
  Lemma simple_subsume_place_rty_to_ty_r (ty1 ty2 : rtype) x P {Heq: ty1.(rty_type) = ty2.(rty_type)} `{!SimpleSubsumePlace (x @ ty1) ((rew [λ x : Type, x] Heq in x) @ ty2) P} :
    SimpleSubsumePlace (x @ ty1) ty2 P.
  Proof. iIntros (l β) "HP Hl". iExists (rew [λ x : Type, x] Heq in x). iApply (@simple_subsume_place with "HP Hl"). Qed.


  Lemma subtype_var {A} (ty : A → type) x y l β T:
    ⌜x = y⌝ ∗ T -∗
    subsume (l ◁ₗ{β} ty x) (l ◁ₗ{β} ty y) T.
  Proof. iIntros "[-> $] $". Qed.
  (* This must be an hint extern because an instance would be a big slowdown . *)
  Definition subtype_var_inst {A} (ty : A → type) x y l β : SubsumePlace l β (ty x) (ty y) :=
    λ T, i2p (subtype_var ty x y l β T).

  Lemma typed_binop_simplify v1 P1 v2 P2 T o1 o2 ot1 ot2 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} op:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_bin_op v1 P v2 P2 op ot1 ot2 T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_bin_op v1 P1 v2 P op ot1 ot2 T))).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then G2 else G1
     | Some n1, _ => G1
     | _, _ => G2
       end in
    G -∗ typed_bin_op v1 P1 v2 P2 op ot1 ot2 T.
  Proof.
    iIntros "Hs Hv1 Hv2".
    destruct o1 as [n1|], o2 as [n2|] => //. case_match.
    1,3,4: iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    4,5,6: iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$]").
  Qed.
  Global Instance typed_binop_simplify_inst v1 P1 v2 P2 o1 o2 ot1 ot2 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} op `{!TCOneIsSome o1 o2} :
    TypedBinOp v1 P1 v2 P2 op ot1 ot2 | 1000 :=
    λ T, i2p (typed_binop_simplify v1 P1 v2 P2 T o1 o2 ot1 ot2 op).

  Lemma typed_unop_simplify v P T n ot {SH : SimplifyHyp P (Some n)} op:
    (SH (find_in_context (FindValP v) (λ P, typed_un_op v P op ot T))).(i2p_P) -∗
    typed_un_op v P op ot T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as (P') "[Hv Hsub]". simpl in *. by iApply ("Hsub" with "[$]").
  Qed.
  Global Instance typed_unop_simplify_inst v P n ot {SH : SimplifyHyp P (Some n)} op :
    TypedUnOp v P op ot | 1000 :=
    λ T, i2p (typed_unop_simplify v P T n ot op).

  Lemma typed_copy_alloc_id_simplify v1 P1 v2 P2 T o1 o2 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2}:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_copy_alloc_id v1 P v2 P2 T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_copy_alloc_id v1 P1 v2 P T))).(i2p_P) in
    let G :=
       match o1, o2 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then G2 else G1
     | Some n1, _ => G1
     | _, _ => G2
       end in
    G -∗ typed_copy_alloc_id v1 P1 v2 P2 T.
  Proof.
    iIntros "Hs Hv1 Hv2".
    destruct o1 as [n1|], o2 as [n2|] => //. case_match.
    1,3,4: iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    4,5,6: iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$]").
  Qed.
  Global Instance typed_copy_alloc_id_simplify_inst v1 P1 v2 P2 o1 o2 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} `{!TCOneIsSome o1 o2} :
    TypedCopyAllocId v1 P1 v2 P2 | 1000 :=
    λ T, i2p (typed_copy_alloc_id_simplify v1 P1 v2 P2 T o1 o2).

  Lemma typed_cas_simplify v1 P1 v2 P2 v3 P3 T ot o1 o2 o3 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} {SH3 : SimplifyHyp P3 o3}:
    let G1 := (SH1 (find_in_context (FindValP v1) (λ P, typed_cas ot v1 P v2 P2 v3 P3 T))).(i2p_P) in
    let G2 := (SH2 (find_in_context (FindValP v2) (λ P, typed_cas ot v1 P1 v2 P v3 P3 T))).(i2p_P) in
    let G3 := (SH3 (find_in_context (FindValP v3) (λ P, typed_cas ot v1 P1 v2 P2 v3 P T))).(i2p_P) in
    let min o1 o2 :=
       match o1.1, o2.1 with
     | Some n1, Some n2 => if (n2 ?= n1)%N is Lt then o2 else o1
     | Some n1, _ => o1
     | _, _ => o2
       end in
    let G := (min (o1, G1) (min (o2, G2) (o3, G3))).2 in
    G -∗ typed_cas ot v1 P1 v2 P2 v3 P3 T.
  Proof.
    iIntros "Hs Hv1 Hv2 Hv3".
    destruct o1 as [n1|], o2 as [n2|], o3 as [n3|] => //=; repeat case_match => /=.
    all: try iDestruct (i2p_proof with "Hs Hv1") as (P) "[Hv Hsub]".
    all: try iDestruct (i2p_proof with "Hs Hv2") as (P) "[Hv Hsub]".
    all: try iDestruct (i2p_proof with "Hs Hv3") as (P) "[Hv Hsub]".
    all: by simpl in *; iApply ("Hsub" with "[$] [$]").
  Qed.
  Global Instance typed_cas_simplify_inst v1 P1 v2 P2 v3 P3 ot o1 o2 o3 {SH1 : SimplifyHyp P1 o1} {SH2 : SimplifyHyp P2 o2} {SH3 : SimplifyHyp P3 o3} `{!TCOneIsSome3 o1 o2 o3} :
    TypedCas ot v1 P1 v2 P2 v3 P3 | 1000 :=
    λ T, i2p (typed_cas_simplify v1 P1 v2 P2 v3 P3 T ot o1 o2 o3).

  Lemma typed_annot_stmt_simplify A (a : A) l P T n {SH : SimplifyHyp P (Some n)}:
    (SH (find_in_context (FindLoc l) (λ '(β1, ty1),
       typed_annot_stmt a l (l ◁ₗ{β1} ty1) T))).(i2p_P) -∗
    typed_annot_stmt a l P T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as ([β1 ty1]) "[Hl Hannot]" => /=.
      by iApply ("Hannot" with "[$]").
  Qed.
  Global Instance typed_annot_stmt_simplify_inst A (a : A) l P n {SH : SimplifyHyp P (Some n)}:
    TypedAnnotStmt a l P | 1000 :=
    λ T, i2p (typed_annot_stmt_simplify A a l P T n).

  Lemma typed_annot_expr_simplify A m (a : A) v P T n {SH : SimplifyHyp P (Some n)}:
    (SH (find_in_context (FindValP v) (λ Q,
       typed_annot_expr m a v Q T))).(i2p_P) -∗
    typed_annot_expr m a v P T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as ([β1 ty1]) "[Hl Hannot]" => /=.
      by iApply ("Hannot" with "[$]").
  Qed.
  Global Instance typed_annot_expr_simplify_inst A m (a : A) v P n {SH : SimplifyHyp P (Some n)}:
    TypedAnnotExpr m a v P | 1000 :=
    λ T, i2p (typed_annot_expr_simplify A m a v P T n).

  (*** statements *)
  Global Instance elim_modal_bupd_typed_stmt B p s fn ls R Q P :
    ElimModal True p false (|==> P) P (typed_stmt (B:=B) s fn ls R Q) (typed_stmt (B:=B) s fn ls R Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim (bupd_fupd ⊤) fupd_frame_r bi.wand_elim_r.
    iIntros "_ Hs ?". iMod "Hs". by iApply "Hs".
  Qed.

  Global Instance elim_modal_fupd_typed_stmt B p s fn ls R Q P :
    ElimModal True p false (|={⊤}=> P) P (typed_stmt (B:=B) s fn ls R Q) (typed_stmt (B:=B) s fn ls R Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim fupd_frame_r bi.wand_elim_r.
    iIntros "_ Hs ?". iMod "Hs". by iApply "Hs".
  Qed.

  Lemma type_goto {B} Q b fn ls (fr : B → _) s:
    Q !! b = Some s →
    typed_stmt s fn ls fr Q -∗
    typed_stmt (Goto b) fn ls fr Q.
  Proof.
    iIntros (HQ) "Hs". iIntros (Hls). iApply wps_goto => //.
    iModIntro. by iApply "Hs".
  Qed.

  Lemma type_goto_precond {B} P Q b fn ls (fr : B → _):
    (typed_block P b fn ls fr Q ∗ P ∗ True) -∗
    typed_stmt (Goto b) fn ls fr Q.
  Proof.
    iIntros "[Hblock [HP _]]" (Hls).
    by iApply "Hblock".
  Qed.

  Lemma type_assign {B} ly e1 e2 Q s fn ls (fr : B → _) o:
    typed_val_expr e2 (λ v ty, ⌜ty.(ty_layout) = ly⌝ ∗ ⌜if o is Na2Ord then False else True⌝ ∗
      typed_write (if o is ScOrd then true else false) e1 v ty (typed_stmt s fn ls fr Q)) -∗
    typed_stmt (e1 <-{ly, o} e2; s) fn ls fr Q.
  Proof.
    iIntros "He" (Hls).
    wps_bind. iApply "He". iIntros (v ty) "Hv [<- [% He1]]".
    wps_bind. iApply "He1". iIntros (l) "HT".
    iDestruct (ty_size_eq with "Hv") as %?.
    iApply wps_assign; rewrite ?val_to_of_loc //. destruct o; naive_solver.
    iMod ("HT" with "Hv") as "[$ HT]". destruct o; iIntros "!# !# Hl".
    all: by iApply ("HT" with "Hl").
  Qed.

  Lemma type_if {B} Q e s1 s2 fn ls (fr : B → _):
    typed_val_expr e (λ v ty, typed_if (IntOp bool_it) v ty
          (typed_stmt s1 fn ls fr Q) (typed_stmt s2 fn ls fr Q)) -∗
    typed_stmt (if: e then s1 else s2) fn ls fr Q.
  Proof.
    iIntros "He" (Hls). wps_bind.
    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as (it z ? Hn) "Hs". simplify_eq.
    iApply wps_if => //.
    by case_decide; iApply "Hs".
  Qed.

  Lemma type_switch {B} Q it e m ss def fn ls (fr : B → _):
    typed_val_expr e (λ v ty, typed_switch v ty it m ss def fn ls fr Q) -∗
    typed_stmt (Switch it e m ss def) fn ls fr Q.
  Proof.
    iIntros "He" (Hls).
    have -> : (Switch it e m ss def) = (W.to_stmt (W.Switch it (W.Expr e) m (W.Stmt <$> ss) (W.Stmt def)))
      by rewrite /W.to_stmt/= -!list_fmap_compose list_fmap_id.
    iApply tac_wps_bind; first done.
    rewrite /W.to_expr /W.to_stmt /= -list_fmap_compose list_fmap_id.

    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as (z Hn) "Hs".
    iAssert (⌜∀ i : nat, m !! z = Some i → is_Some (ss !! i)⌝%I) as %?. {
      iIntros (i ->). iDestruct "Hs" as (s ->) "_"; by eauto.
    }
    iApply wps_switch; [done..|].
    destruct (m !! z) => /=.
    - iDestruct "Hs" as (s ->) "Hs". by iApply "Hs".
    - by iApply "Hs".
  Qed.

  Lemma type_assert {B} Q e s fn ls (fr : B → _):
    typed_val_expr e (λ v ty, typed_assert v ty s fn ls fr Q) -∗
    typed_stmt (assert: e; s) fn ls fr Q.
  Proof.
    iIntros "He" (Hls). wps_bind.
    iApply "He". iIntros (v ty) "Hv Hs".
    iDestruct ("Hs" with "Hv") as (z Hn Hz) "Hs".
    iApply wps_assert => //.
    by iApply "Hs".
  Qed.

  Lemma type_exprs {B} s e fn ls (fr : B → _) Q:
    (typed_val_expr e (λ v ty, v ◁ᵥ ty -∗ typed_stmt s fn ls fr Q)) -∗ typed_stmt (ExprS e s) fn ls fr Q.
  Proof.
    iIntros "Hs ?". wps_bind. iApply "Hs". iIntros (v ty) "Hv Hs".
    iApply wps_exprs. iApply step_fupd_intro => //. iModIntro.
    by iApply ("Hs" with "Hv").
  Qed.

  Lemma type_skips {B} s fn ls Q (fr : B → _):
    (|={⊤}[∅]▷=> typed_stmt s fn ls fr Q) -∗ typed_stmt (SkipS s) fn ls fr Q.
  Proof.
    iIntros "Hs ?". iApply wps_skip. iApply (step_fupd_wand with "Hs"). iIntros "Hs". by iApply "Hs".
  Qed.

  Lemma type_skips' {B} s fn ls Q (fr : B → _):
    typed_stmt s fn ls fr Q -∗ typed_stmt (SkipS s) fn ls fr Q.
  Proof. iIntros "Hs". iApply type_skips. by iApply step_fupd_intro. Qed.

  Lemma type_annot_stmt {A B} p (a : A) s fn ls Q (fr : B → _):
    (typed_addr_of p (λ l β ty, typed_annot_stmt a l (l ◁ₗ{β} ty) (typed_stmt s fn ls fr Q))) -∗
      typed_stmt (annot: a; expr: &p; s) fn ls fr Q.
  Proof.
    iIntros "Hs ?". iApply wps_annot => /=.
    wps_bind. rewrite /AddrOf. iApply "Hs".
    iIntros (l β ty) "Hl Ha". iApply wps_exprs.
      by iApply ("Ha" with "Hl").
  Qed.

  Lemma typed_block_rec {B} Ps Q fn ls (fr : B → _) s:
    ([∗ map] b ↦ P ∈ Ps, ∃ s, ⌜Q !! b = Some s⌝ ∗ □(([∗ map] b ↦ P ∈ Ps, typed_block P b fn ls fr Q) -∗ P -∗ typed_stmt s fn ls fr Q)) -∗
    (([∗ map] b ↦ P ∈ Ps, typed_block P b fn ls fr Q) -∗ typed_stmt s fn ls fr Q) -∗
    typed_stmt s fn ls fr Q.
  Proof.
    iIntros "HQ Hs" (Hls).
    iApply ("Hs" with "[HQ]"); last done.
    iApply wps_block_rec.
    iApply (big_sepM_mono with "HQ").
    iIntros (b P Hb) => /=.
    repeat f_equiv. iIntros "Hs". by iApply "Hs".
  Qed.

  (*** expressions *)
  Lemma type_val_context v T:
    (find_in_context (FindVal v) T) -∗
    typed_value v T.
  Proof.
    iDestruct 1 as (ty) "[Hv HT]". simpl in *.
    iExists _. iFrame.
  Qed.
  Global Instance type_val_context_inst v :
    TypedValue v | 100 := λ T, i2p (type_val_context v T).

  Lemma type_val v T:
    typed_value v (T v) -∗
    typed_val_expr (Val v) T.
  Proof.
    iIntros "HP" (Φ) "HΦ".
    iDestruct "HP" as (ty) "[Hv HT]".
    iApply wp_value. iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_bin_op o e1 e2 ot1 ot2 T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, typed_bin_op v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) o ot1 ot2 T)) -∗
    typed_val_expr (BinOp o ot1 ot2 e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    wp_bind. iApply "He2". iIntros (v2 ty2) "Hv2 Hop".
    by iApply ("Hop" with "Hv1 Hv2").
  Qed.

  Lemma type_un_op o e ot T:
    typed_val_expr e (λ v ty, typed_un_op v (v ◁ᵥ ty) o ot T) -∗
    typed_val_expr (UnOp o ot e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv Hop".
    by iApply ("Hop" with "Hv").
  Qed.

  Lemma type_copy_alloc_id e1 e2 T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, typed_copy_alloc_id v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) T)) -∗
    typed_val_expr (CopyAllocId e1 e2) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    wp_bind. iApply "He2". iIntros (v2 ty2) "Hv2 Hop".
    by iApply ("Hop" with "Hv1 Hv2").
  Qed.

  Lemma type_cas ot e1 e2 e3 T:
    typed_val_expr e1 (λ v1 ty1, typed_val_expr e2 (λ v2 ty2, typed_val_expr e3 (λ v3 ty3, typed_cas ot v1 (v1 ◁ᵥ ty1) v2 (v2 ◁ᵥ ty2) v3 (v3 ◁ᵥ ty3) T))) -∗
    typed_val_expr (CAS ot e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 He2".
    wp_bind. iApply "He2". iIntros (v2 ty2) "Hv2 He3".
    wp_bind. iApply "He3". iIntros (v3 ty3) "Hv3 Hop".
    by iApply ("Hop" with "Hv1 Hv2 Hv3").
  Qed.

  Lemma type_ife ot e1 e2 e3 T:
    typed_val_expr e1 (λ v ty, typed_if ot v ty (typed_val_expr e2 T) (typed_val_expr e3 T)) -∗
    typed_val_expr (IfE ot e1 e2 e3) T.
  Proof.
    iIntros "He1" (Φ) "HΦ".
    wp_bind. iApply "He1". iIntros (v1 ty1) "Hv1 Hif".
    iDestruct ("Hif" with "Hv1") as (it n -> ?) "HT".
    iApply wp_if => //.
    by case_decide; iApply "HT".
  Qed.

  Lemma type_skipe e T:
    typed_val_expr e (λ v ty, |={⊤}[∅]▷=> T v ty) -∗ typed_val_expr (SkipE e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT".
    iApply (wp_step_fupd with "HT") => //.
    iApply wp_skip. iIntros "!> HT !>".
    by iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_skipe' e T:
    typed_val_expr e T -∗ typed_val_expr (SkipE e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT".
    iApply wp_skip. by iApply ("HΦ" with "Hv HT").
  Qed.

  Lemma type_annot_expr n {A} (a : A) e T:
    typed_val_expr e (λ v ty, typed_annot_expr n a v (v ◁ᵥ ty) (find_in_context (FindVal v) (λ ty, T v ty))) -∗
    typed_val_expr (AnnotExpr n a e) T.
  Proof.
    iIntros "He" (Φ) "HΦ".
    wp_bind. iApply "He". iIntros (v ty) "Hv HT". iDestruct ("HT" with "Hv") as "HT".
    iInduction n as [|n] "IH" forall (Φ). {
      rewrite /AnnotExpr/=.
      iApply fupd_wp.
      iMod "HT" as (?) "[HT ?] /=". iApply wp_value.
      iApply ("HΦ" with "[$] [$]").
    }
    rewrite annot_expr_S_r. wp_bind.
    iApply (wp_step_fupd with "HT") => //.
    iApply wp_skip. iIntros "!> HT !>".
    by iApply ("IH" with "HΦ HT").
  Qed.

  Lemma type_macro_expr m es T:
    typed_macro_expr m es T -∗
    typed_val_expr (MacroE m es) T.
  Proof. done. Qed.

  Lemma type_use ly T e o:
    ⌜if o is Na2Ord then False else True⌝ ∗ typed_read (if o is ScOrd then true else false) e ly T -∗
    typed_val_expr (use{ly, o} e) T.
  Proof.
    iIntros "[% Hread]" (Φ) "HΦ".
    wp_bind. iApply "Hread".
    iIntros (l) "Hl". rewrite /Use.
    destruct o => //.
    1: iApply wp_atomic.
    2: iApply fupd_wp; iApply wp_fupd.
    all: iMod "Hl" as (v q ty Hly Hv) "(Hl&Hv&HT)"; iModIntro.
    all: iDestruct (ty_size_eq with "Hv") as "#>%".
    all: iApply (wp_deref with "Hl") => //; try by eauto using val_to_of_loc.
    all: iIntros "!# Hl".
    all: iMod ("HT" with "Hl"); iModIntro.
    all: by iApply ("HΦ" with "Hv").
  Qed.

  Lemma type_read T T' e ly a:
    IntoPlaceCtx e T' →
    T' (λ K l, find_in_context (FindLoc l) (λ '(β1, ty1),
      typed_place K l β1 ty1 (λ l2 β2 ty2 typ R,
          typed_read_end a l2 β2 ty2 ly (λ v ty2' (ty3 : mtype),
            l ◁ₗ{β1} typ ty2' -∗ R ty2' -∗ T v ty3)))) -∗
    typed_read a e ly T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "HΦ".
    iApply (HT' with "HT'").
    iIntros (K l). iDestruct 1 as ([β ty]) "[Hl HP]".
    iApply ("HP" with "Hl").
    iIntros (l' β2 ty2 typ R) "Hl' Hc HT" => /=. iApply "HΦ".
    iMod ("HT" with "Hl'") as (q v ty' ty3 Hly Hv) "(Hl&Hv&HT)".
    iModIntro. iExists _,_,_. iFrame. iSplit => //. iSplit => //.
    iIntros "!# Hl". iMod ("HT" with "Hl") as "[Hl HT]".
    iMod ("Hc" with "Hl") as "[? ?]". by iApply ("HT" with "[$]").
  Qed.

  Lemma type_read_copy T β l ty ly a {HC: CopyAs l β ty}:
    ((HC (λ ty', ⌜ty'.(ty_layout) = ly⌝ ∗ ∀ v, T v (ty' : type) ty')).(i2p_P)) -∗
      typed_read_end a l β ty ly T.
  Proof.
    iIntros "Hs Hl". iDestruct (i2p_proof with "Hs Hl") as (ty') "(Hl&%&<-&HT)".
    iRevert "Hl". destruct β.
    - iIntros "Hl".
      iMod (fupd_intro_mask') as "Hclose". 2: iModIntro. by destruct a; set_solver.
      iDestruct (ty_aligned with "Hl") as %?.
      iDestruct (ty_deref with "Hl") as (v) "[Hl #Hv]".
      iDestruct (ty_size_eq with "Hv") as %?.
      iExists _, _, _, _. iFrame "∗Hv". do 2 iSplitR => //=.
      iIntros "!# Hl". iMod "Hclose". iModIntro. iSplitR "HT" => //.
        by iApply (ty_ref with "[//] Hl Hv").
    - iIntros "#Hl".
      iMod (copy_shr_acc with "Hl") as (? q' v) "[Hmt [Hv Hc]]" => //.
      iDestruct (ty_size_eq with "Hv") as "#>%".
      iMod (fupd_intro_mask') as "Hclose". 2: iModIntro. by destruct a; set_solver.
      iExists _, _, _, _. iFrame. do 2 iSplit => //=.
      iIntros "!# Hmt". iMod "Hclose". iModIntro. by iSplitR "HT".
  Qed.

  Global Instance type_read_copy_inst β l ty ly a `{!CopyAs l β ty} :
    TypedReadEnd a l β ty ly | 10 :=
    λ T, i2p (type_read_copy T β l ty ly a).

  Lemma type_write a ty `{!Movable ty} T T' e v:
    IntoPlaceCtx e T' →
    T' (λ K l, find_in_context (FindLoc l) (λ '(β1, ty1),
      typed_place K l β1 ty1 (λ l2 β2 ty2 typ R,
         typed_write_end a v ty l2 β2 ty2 (λ ty3, l ◁ₗ{β1} typ ty3 -∗ R ty3 -∗ T)))) -∗
    typed_write a e v ty T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "HΦ".
    iApply (HT' with "HT'"). iIntros (K l). iDestruct 1 as ([β1 ty1]) "[Hl HK]".
    iApply ("HK" with "Hl"). iIntros (l2 β2 ty2 typ R) "Hl' Hc He".
    iApply "HΦ". iIntros "Hv". iMod ("He" with "Hl' Hv") as "[$ Hc2]". iModIntro.
    iIntros "!# Hl".
    iMod ("Hc2" with "Hl") as (ty3) "[Hl HT]".
    iMod ("Hc" with "Hl") as "[? ?]". by iApply ("HT" with "[$]").
  Qed.

  (* TODO: this constraint on the layout is too strong, we only need
  that the length is the same and the alignment is lower. Adapt when necessary. *)
  Lemma type_write_own_copy a ty `{!Movable ty} T l2 ty2 v `{!Movable ty2} `{!Copyable ty}:
    ⌜ty2.(ty_layout) = ty.(ty_layout)⌝ ∗ (v ◁ᵥ ty -∗ T ty) -∗
    typed_write_end a v ty l2 Own ty2 T.
  Proof.
    iDestruct 1 as (Heq) "HT". iIntros "Hl #Hv".
    iDestruct (ty_aligned with "Hl") as %?.
    iDestruct (ty_deref with "Hl") as (v') "[Hl Hv']".
    iDestruct (ty_size_eq with "Hv'") as %?.
    iMod (fupd_intro_mask' _ (if a then ∅ else ⊤)) as "Hmask" => //. iModIntro.
    iSplitL "Hl". by iExists _; iFrame; rewrite -Heq.
    iIntros "!# Hl". iMod "Hmask". iModIntro.
    iDestruct (ty_size_eq with "Hv") as %?.
    iExists _. iDestruct ("HT" with "Hv") as "$".
    iApply (ty_ref with "[] Hl Hv"). by rewrite -Heq.
  Qed.
  Global Instance type_write_own_copy_inst a ty `{!Movable ty} l2 ty2 v `{!Movable ty2} `{!Copyable ty}:
    TypedWriteEnd a v ty l2 Own ty2 | 20 :=
    λ T, i2p (type_write_own_copy a ty T l2 ty2 v).

  Lemma type_addr_of_place T T' e:
    IntoPlaceCtx e T' →
    T' (λ K l, find_in_context (FindLoc l) (λ '(β1, ty1),
      typed_place K l β1 ty1 (λ l2 β2 ty2 typ R,
                              typed_addr_of_end l2 β2 ty2 (λ β3 ty3 ty',
                  l ◁ₗ{β1} typ ty' -∗ R ty' -∗ T l2 β3 ty3)))) -∗
    typed_addr_of e T.
  Proof.
    iIntros (HT') "HT'". iIntros (Φ) "HΦ".
    iApply @wp_fupd. iApply (HT' with "HT'").
    iIntros (K l). iDestruct 1 as ([β ty]) "[Hl HP]".
    iApply ("HP" with "Hl"). iIntros (l2 β2 ty2 typ R) "Hl' Hc HT".
    iMod ("HT" with "Hl'") as (β3 ty3 ty') "[Hty3 [Hty' HT]]".
    iMod ("Hc" with "Hty'") as "[Hc ?]". iModIntro.
    iApply ("HΦ" with "Hty3").
    by iApply ("HT" with "[$]").
  Qed.


  Lemma type_place_id l ty β T:
    T l β ty id (λ _, True) -∗
    typed_place [] l β ty T.
  Proof.
    iIntros "HT" (Φ) "Hl HΦ". iApply ("HΦ" with "Hl [] HT").  by iIntros (ty') "$".
  Qed.
  (* This should have priority over e.g. the place instance of padded *)
  Global Instance type_place_id_inst l ty β:
    TypedPlace [] l β ty | 20 := λ T, i2p (type_place_id l ty β T).

  Lemma copy_as_id l β ty `{!Movable ty} `{!Copyable ty} T:
    T (t2mt ty) -∗ copy_as l β ty T.
  Proof. iIntros "HT Hl". iExists (t2mt _). by iFrame. Qed.
  Global Instance copy_as_id_inst l β ty `{!Movable ty} `{!Copyable ty}:
    CopyAs l β ty | 1000 := λ T, i2p (copy_as_id l β ty T).

  Lemma copy_as_refinement l β (ty : rtype) {HC: ∀ x, CopyAs l β (x @ ty)} T:
    (∀ x, (HC x T).(i2p_P)) -∗ copy_as l β ty T.
  Proof.
    iIntros "HT Hl". iDestruct "Hl" as (x) "Hl".
    iSpecialize ("HT" $! x). iDestruct (i2p_proof with "HT") as "HT". by iApply "HT".
  Qed.
  Global Instance copy_as_refinement_inst l β (ty : rtype) {HC: ∀ x, CopyAs l β (x @ ty)}:
    CopyAs l β ty := λ T, i2p (copy_as_refinement l β ty T).

  Lemma annot_share l ty T:
    (l ◁ₗ{Shr} ty -∗ T) -∗
    typed_annot_stmt (ShareAnnot) l (l ◁ₗ ty) T.
  Proof.
    iIntros "HT Hl". iMod (ty_share with "Hl") => //.
    iApply step_fupd_intro => //. iModIntro. by iApply "HT".
  Qed.
  Global Instance annot_share_inst l ty:
    TypedAnnotStmt (ShareAnnot) l (l ◁ₗ ty) :=
    λ T, i2p (annot_share l ty T).

  Lemma annot_stop l β ty T:
    (l ◁ₗ{β} ty -∗ False) -∗
    typed_annot_stmt (StopAnnot) l (l ◁ₗ{β} ty) T.
  Proof. iIntros "HT Hl". iDestruct ("HT" with "Hl") as %[]. Qed.
  Global Instance annot_stop_inst l β ty:
    TypedAnnotStmt (StopAnnot) l (l ◁ₗ{β} ty) :=
    λ T, i2p (annot_stop l β ty T).

  Lemma annot_unfold_once l β ty T n {SH : SimplifyHyp (l ◁ₗ{β} ty) (Some (Npos n))}:
    (SH T).(i2p_P) -∗
    typed_annot_stmt UnfoldOnceAnnot l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "Hs Hv". iDestruct (i2p_proof with "Hs Hv") as "HT" => /=.
    by iApply step_fupd_intro.
  Qed.
  Global Instance annot_unfold_once_inst l β ty n {SH : SimplifyHyp (l ◁ₗ{β} ty) (Some (Npos n))}:
    TypedAnnotStmt UnfoldOnceAnnot l (l ◁ₗ{β} ty) :=
    λ T, i2p (annot_unfold_once l β ty T n).

  Lemma annot_learn l β ty T {L : Learnable (l ◁ₗ{β} ty)}:
    (learnable_data ∗ l ◁ₗ{β} ty -∗ T) -∗
    typed_annot_stmt (LearnAnnot) l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "HT Hl". iApply step_fupd_intro => //.
    iDestruct (learnable_learn with "Hl") as "#H".
    iApply "HT". by iFrame.
  Qed.
  Global Instance annot_learn_inst l β ty {L : Learnable (l ◁ₗ{β} ty)}:
    TypedAnnotStmt (LearnAnnot) l (l ◁ₗ{β} ty) :=
    λ T, i2p (annot_learn l β ty T).

  Lemma annot_learn_aligment l β ty T {L : LearnAlignment β ty}:
    (⌜l `aligned_to` learnalign_align L⌝ -∗ l ◁ₗ{β} ty -∗ T) -∗
    typed_annot_stmt (LearnAlignment) l (l ◁ₗ{β} ty) T.
  Proof.
    iIntros "HT Hl". iApply step_fupd_intro => //. iModIntro.
    iDestruct ((learnalign_learn L) with "Hl") as %?.
    by iApply "HT".
  Qed.
  Global Instance annot_learn_align_inst l β ty {L : LearnAlignment β ty}:
    TypedAnnotStmt (LearnAlignmentAnnot) l (l ◁ₗ{β} ty) :=
    λ T, i2p (annot_learn_aligment l β ty T).
End typing.

(* This must be an hint extern because an instance would be a big slowdown . *)
Hint Extern 1 (SubsumePlace _ _ (?ty _) (?ty2 _)) =>
  match ty with | ty2 => is_var ty; class_apply subtype_var_inst end : typeclass_instances.

(*** guarded *)
Section guarded.
  Context `{!typeG Σ}.

  Definition guardedN : namespace := nroot.@"guardedN".

  (* The name space is necessary for stripping the later and distinghishing different guardeds *)
  Program Definition guarded (n : string) (ty : type) : type := {|
    ty_own β l := match β return _ with
                  | Own => ▷ l ◁ₗ ty
                  | Shr => □ ∀ E, ⌜↑shrN ⊆ E⌝ -∗ ⌜↑guardedN.@n ⊆ E⌝ ={E}[E ∖ ↑guardedN.@n]▷=∗ l ◁ₗ{Shr} ty
                  end%I;
  |}.
  Next Obligation.
    (* This is taken from the delayed shring approach in RustBelt. *)
    iIntros (n ty l ? ?) "Hl".
    iMod (inv_alloc (guardedN.@n) _ (l ◁ₗ ty ∨ l ◁ₗ{Shr} ty)%I
          with "[Hl]") as "#Hinv"; first by eauto.
    iIntros "!# !#" (E' Hshr Hguard).
    iMod (inv_acc with "Hinv") as "[INV Hclose]"; first solve_ndisj.
    iIntros "!# !#". iDestruct "INV" as "[Hl|#Hl]".
    1: iMod (ty_share with "Hl") as "#Hl"; first solve_ndisj.
    all: iMod ("Hclose" with "[]"); by iFrame "Hl".
  Qed.

  Global Instance guarded_contractive n : Contractive (guarded n).
  Proof. constructor. solve_contractive. Qed.

  Lemma guarded_intro n l β ty :
    l ◁ₗ{β} ty -∗ l ◁ₗ{β} guarded n ty.
  Proof.
    rewrite {2}/ty_own. destruct β; simpl; first by iIntros "$".
    iIntros "#$ !#" (???). iApply step_fupd_intro => //. solve_ndisj.
  Qed.

  Lemma guarded_elim n l β ty E :
    ↑shrN ⊆ E → ↑guardedN.@n ⊆ E →
    l ◁ₗ{β} guarded n ty ={E}[E ∖ ↑guardedN.@n]▷=∗ l ◁ₗ{β} ty.
  Proof.
    move => ??. rewrite {1}/ty_own. destruct β => /=.
    - iIntros "$". iApply step_fupd_intro => //. solve_ndisj.
    - iIntros "#H". by iApply "H".
  Qed.

  Lemma simplify_goal_place_guarded n ty l β T:
    T (l ◁ₗ{β} ty) -∗
    simplify_goal (l◁ₗ{β} guarded n ty) T.
  Proof. iIntros "HT". iExists _. iFrame. by iApply guarded_intro. Qed.
  Global Instance simplify_goal_place_guarded_inst n ty l β:
    SimplifyGoalPlace l β (guarded n ty) (Some 0%N) :=
    λ T, i2p (simplify_goal_place_guarded n ty l β T).

  Global Instance simple_subsume_place_guarded n ty1 ty2 P `{!SimpleSubsumePlace ty1 ty2 P} :
    SimpleSubsumePlace ty1 (guarded n ty2) P.
  Proof. iIntros (l β) "HP Hl". iApply guarded_intro. iApply (@simple_subsume_place with "HP Hl"). Qed.

  (*
    This class should be implemented but not directly be used as a premise.
   E1: elements needed in the mask, E2: elements needed in the mask and removed during the step.
   E1, E2, ty2 are outputs. *)
  Class StripGuarded (β : own_state) (E1 E2 : coPset) (ty1 ty2 : type) : Prop :=
    strip_guarded l E : E1 ⊆ E → E2 ⊆ E → l ◁ₗ{β} ty1 ={E}[E ∖ E2]▷=∗ l ◁ₗ{β} ty2.

  Global Instance strip_guarded_id β ty : StripGuarded β ∅ ∅ ty ty | 1000.
  Proof. iIntros (l E _ _) "$". iApply step_fupd_intro => //. solve_ndisj. Qed.

  Global Instance strip_guarded_guarded n β ty : StripGuarded β (↑shrN) (↑guardedN.@n) (guarded n ty) ty.
  Proof. iIntros (l E H1 H2). by iApply guarded_elim. Qed.


  Class StripGuardedLst (β : own_state) (E1 E2 : coPset) (tys1 tys2 : list type) : Prop :=
    strip_guarded_lst ls E : E1 ⊆ E → E2 ⊆ E → ([∗ list] l;ty1∈ls;tys1, l ◁ₗ{β} ty1) ={E}[E ∖ E2]▷=∗ ([∗ list] l;ty2∈ls;tys2, l ◁ₗ{β} ty2).

  Global Instance strip_guarded_lst_strip β E1 E2 Es1 Es2 ty1 ty2 tys1 tys2 `{!StripGuarded β E1 E2 ty1 ty2} `{!StripGuardedLst β Es1 Es2 tys1 tys2} Er1 Er2
         (* We want to have as few calls to CoPsetFact as possible and
         keep Er1 and Er2 as simple as possible. This is why we
         special case the empty set. *)
         `{!TCIf (TCEq E1 ∅)
            (TCEq Er1 Es1)
            (TCIf (TCEq Es1 ∅)
                  (TCEq Er1 E1)
                  (TCEq Er1 (E1 ∪ Es1)))}
         `{!TCIf (TCEq E2 ∅)
            (TCEq Er2 Es2)
            (TCIf (TCEq Es2 ∅)
                  (TCAnd (TCEq Er2 E2) (CoPsetFact (E2 ## Es1)))
                  (TCAnd (TCEq Er2 (E2 ∪ Es2)) (TCAnd (CoPsetFact (E2 ## Es1)) (CoPsetFact (E2 ## Es2)))))} :
    StripGuardedLst β Er1 Er2 (ty1 :: tys1) (ty2 :: tys2) | 10.
  Proof.
    iIntros (ls E HE1 HE2) "Hls". iDestruct (big_sepL2_cons_inv_r with "Hls") as (l ls' ->) "[Hl Hls]".
    have [?[?[??]]]: Er1 = (E1 ∪ Es1) ∧ Er2 = (E2 ∪ Es2) ∧ E2 ## Es1 ∧ (E2 ## Es2). {
      repeat match goal with
      | H : TCIf _ _ _ |- _ => inversion_clear H
      | H : TCEq _ _ |- _ => inversion_clear H
      | H : TCAnd _ _ |- _ => inversion_clear H
      end; set_solver.
    }
    subst.
    iMod (strip_guarded with "Hl") as "Hl"; [solve_ndisj..|].
    iMod (strip_guarded_lst with "Hls") as "Hls"; [solve_ndisj..|].
    rewrite difference_difference_L.
    iIntros "!# !#".
    rewrite -difference_difference_L.
    iMod "Hls". iMod "Hl". iModIntro.
    by iFrame.
  Qed.

  Global Instance strip_guarded_lst_skip β  Es1 Es2 ty1 tys1 tys2 `{!StripGuardedLst β Es1 Es2 tys1 tys2} :
    StripGuardedLst β Es1 Es2 (ty1 :: tys1) (ty1 :: tys2) | 50.
  Proof.
    iIntros (ls E HE1 HE2) "Hls". iDestruct (big_sepL2_cons_inv_r with "Hls") as (l ls' ->) "[$ Hls]".
    by iApply strip_guarded_lst.
  Qed.

  Global Instance strip_guarded_lst_nil β :
    StripGuardedLst β ∅ ∅ [] [].
  Proof.
    iIntros (ls E HE1 HE2) "Hls". destruct ls => //=. iApply step_fupd_intro => //. solve_ndisj.
  Qed.

  (* Another layer for performance *)
  Class DoStripGuarded (β : own_state) (E1 E2 : coPset) (ty1 ty2 : type) : Prop :=
    do_strip_guarded : StripGuarded β E1 E2 ty1 ty2.

End guarded.

Hint Mode StripGuarded + + + - - + - : typeclass_instances.
Hint Mode DoStripGuarded + + + - - + - : typeclass_instances.
Hint Mode StripGuardedLst + + + - - + - : typeclass_instances.
Typeclasses Opaque typed_block.

Hint Extern 0 (DoStripGuarded ?β ?E1 ?E2 ?ty1 ?ty2) =>
  change (StripGuarded β E1 E2 ty1 ty2);
  lazymatch ty1 with
  | context [guarded _ _] => idtac
  | _ => notypeclasses refine (strip_guarded_id β ty1)
  end
  : typeclass_instances.

(* Low priority since types might want to have a special form of this
   instance, e.g. optional. The lazymatch is necessary since refine
   sometimes creates the subgoal in a different order. We need to try
   eq first since x1 and x2 in (x1 @ _) and (x2 @ _) might not be
   bound in the scope of P. *)
Hint Extern 99 (SimpleSubsumePlace (_ @ _) (_ @ _) _) =>
    simple notypeclasses refine (simple_subsume_place_refinement_eq _ _ _ _ _ _ _);
      lazymatch goal with
      | |- iProp _ => shelve
      | |- _ = _ => exact : eq_refl
      | |- _ => cbn[eq_rect]
      end : typeclass_instances.
Hint Extern 100 (SimpleSubsumePlace (_ @ _) (_ @ _) _) =>
    simple notypeclasses refine (simple_subsume_place_refinement _ _ _ _ _);
      lazymatch goal with
      | |- iProp _ => shelve
      | |- _ = _ => exact : eq_refl
      | |- _ => cbn[eq_rect]
      end : typeclass_instances.
Hint Extern 100 (SimpleSubsumePlace (_ @ _) (ty_of_rty _) _) =>
  simple notypeclasses refine (simple_subsume_place_rty_to_ty_r _ _ _ _); lazymatch goal with
      | |- iProp _ => shelve
      | |- _ = _ => exact : eq_refl
      | |- _ => cbn[eq_rect]
      end
  : typeclass_instances.
