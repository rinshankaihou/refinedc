From iris.bi Require Export fractional.
From iris.base_logic.lib Require Export invariants.
From refinedc.lang Require Export proofmode notation.
From refinedc.lithium Require Import simpl_classes.
From refinedc.typing Require Export base annotations.
Set Default Proof Using "Type".

Class typeG Σ := TypeG {
  type_heapG :> refinedcG Σ;
}.

(*** type *)
(** There are different for how to model ownership in this type system
and there does not seem to be a perfect one. The options explored so
far are: (ty_own : own_state → loc → iProp Σ )

Owned and shared references:
Inductive own_state : Type := | Own | Shr.
ty_own Own l ={⊤\↑shrN}=∗ ty_own Shr l
Persistent (ty_own Shr l)

This is the simplest option but also the most restrictive:
Once a type is shared it is never possible to unshare it. This might
be enough for Hafnium though. But it seems hard to type e.g. RWLocks with this
model of types. This model is simple because there is no need for recombining
things which is a big source of problems in the other models.

guarded ty:
 Own: ▷ l ◁ₗ{Own} ty
 Shr: □ {|={⊤, ⊤\↑shrN}▷=> l ◁ₗ{Shr} ty
 This could work via the delayed sharing trick of Rustbelt
Lock ty:
 Own: l ↦ b ∗ (l +ₗ 1) ◁ₗ{Own} ty
 Shr: inv lockN (∃ b, l ↦ b ∗ if b then True else (l +ₗ 1) ◁ₗ{Own} ty)
LockGuard ty:
 Own: l ◁ₗ{Shr} Lock ty ∗ (l +ₗ 1) ◁ₗ{Own} ty
 Shr: False ???

Distinct owned and fractional references:
Inductive own_state : Type :=
| Own | Frac (q : Qp).
Definition own_state_to_frac (β : own_state) : Qp :=
  match β with
  | Own => 1%Qp
  | Frac q => q
  end.
Definition own_state_min (β1 β2 : own_state) : own_state :=
  match β1, β2 with
  | Own, Own => Own
  | Frac q, Own => Frac q
  | Own, Frac q => Frac q
  | Frac q, Frac q' => Frac (q * q')
  end.
ty_own Own l ={⊤}=∗ ty_own (Frac 1%Qp) l;
(* ={⊤,∅}▷=∗ would be too strong as we cannot prove it for structs *)
(* maybe you want ={⊤,⊤}▷=∗ here (to strip of the later when going from a frac lock to a owned lock) *
 I think that you actually want the later here since conceptually fractional is one later than the original one (see RustBelt)
 probably you don't want the viewshift after the later, only before it (see inheritance in RustBelt and cancellation of cancellable invariants invariants)*)
ty_own (Frac 1%Qp) l ={⊤}=∗ ty_own Own l;
Fractional (λ q, ty_own (Frac q) l)

Conceptually this seems like the right thing but the splitting of the fractional when combined by the
viewshift and laters causes big problems. Especially it does not seem clear how to define the guarded
type such that it fulfills all the axioms:
guarded ty:
 Own: ▷ l ◁ₗ{Own} ty
 -> does not work because we don't have the viewshift for the frac to own direction

 β: ▷ |={⊤}=> l ◁ₗ{β} ty
 -> does not work because we cannot prove one direction of the Fractional:
 ▷ |={⊤}=> l ◁ₗ{Frac q + p} ty -∗ (▷ |={⊤}=> l ◁ₗ{Frac q} ty) ∗ (▷ |={⊤}=> l ◁ₗ{Frac p} ty)
 -> we don't have a viewshift after stripping the later
 -> a viewshift instead of the entailment does not help either as it does not commute with the later

Only fractional references:
Definition own_state : Type := Qp.
Definition own : own_state := 1%Qp.
Fractional (λ q, ty_own q l)

guarded ty: ▷ l ◁ₗ{q} ty -> should work since ∗ commutes with ▷ in both directions
Lock: exists i, l meta is i and cinv_own i q and inv lock ...

Problem: Lock would not be movable (cannot get the pointsto out without aa viewshift)
Maybe we could add a viewshift when going from own to own val or back
but might not be such a big problem since one could transform it into a movable lock with one step


Other problem with all the Fractional based approaches: you ahve to merge existential quantifiers, which
can come from e.g. refinements.

The right lemma which you want to prove seems to be
∀ q1 q2 x y, P q1 x -∗ P q2 y -∗ P q1 x ∗ P q2 x
This should be provable for most types (e.g. optional assuming l◁ₗ{β} ty -∗ l◁ₗ{β} optty -∗ False)
and it should commute with separating conjuction (necessary for e.g. struct )

We will also probably need a meta like thing in heap lang to associate gnames with locations to ensure that things agree (e.g. gnames used in cancellable invariants lock).

See also http://www0.cs.ucl.ac.uk/staff/J.Brotherston/CAV20/SL_hybrid_perms.pdf



Insight: All approaches above are probably doomed.
Notes:
An additional parameter to shared references is necessary to ensure that you only try to merge related fractions (similar to lifetimes).

This parameter can be used to fix existential quantifiers and the choice inside option. These won't be able to be changed when shared (but when owned).

Owned to shared is a viewshift which creates the value of this parameter.

Question: what should the type of this parameter be? The easiest would be if it is defined by the type but that would probably break fixpoints.
Other option: gname
Other option: Something more complicated like lifetime

Maybe merging and splitting fractions will need a step
We will need an additional parameter

 *)

Definition shrN : namespace := nroot.@"shrN".
Definition mtN : namespace := nroot.@"mtN".
Definition mtE : coPset := ↑mtN.
Inductive own_state : Type :=
| Own | Shr.
Definition own_state_min (β1 β2 : own_state) : own_state :=
  match β1, β2 with
  | Own, Own => Own
  | _, _ => Shr
  end.
Definition heap_mapsto_own_state `{!typeG Σ} (l : loc) (β : own_state) (v : val) : iProp Σ :=
  match β with
  | Own => l↦v
  (* We use many small invariants to be able to prove both directions
  of heap_mapsto_own_state_app. For only ⊢, one big invariant would be
  enough, but not for the other direction since inv_sep only goes in
  one direction. *)
  | Shr => loc_in_bounds l (length v) ∗ [∗ list] i ↦ b ∈ v, inv mtN (∃ q, (l +ₗ i)↦{q} [ b ] )
  end.
Notation "l ↦[ β ] v" := (heap_mapsto_own_state l β v)
  (at level 20, β at level 50, format "l  ↦[ β ]  v") : bi_scope.
Definition heap_mapsto_own_state_layout `{!typeG Σ} (l : loc) (β : own_state) (ly : layout) : iProp Σ :=
  (∃ v, ⌜v `has_layout_val` ly⌝ ∗ ⌜l `has_layout_loc` ly⌝ ∗ l ↦[β] v).
Notation "l ↦[ β ]| ly |" := (heap_mapsto_own_state_layout l β ly)
  (at level 20, β at level 50, format "l  ↦[ β ]| ly |") : bi_scope.

Section own_state.
  Context `{!typeG Σ}.
  Global Instance own_state_min_left_id : LeftId (=) Own own_state_min.
  Proof. by move => []. Qed.
  Global Instance own_state_min_right_id : RightId (=) Own own_state_min.
  Proof. by move => []. Qed.

  Global Instance heap_mapsto_own_state_shr_persistent l v : Persistent (l ↦[ Shr ] v).
  Proof. apply _. Qed.

  Lemma heap_mapsto_own_state_loc_in_bounds l β v :
    l ↦[β] v -∗ loc_in_bounds l (length v).
  Proof.
    destruct β; last by iIntros "[$ _]".
    iIntros "Hl". by iApply heap_mapsto_loc_in_bounds.
  Qed.

  Lemma heap_mapsto_own_state_nil l β:
    l ↦[β] [] ⊣⊢ loc_in_bounds l 0.
  Proof. destruct β; [ by apply heap_mapsto_nil | by rewrite /= right_id ]. Qed.

  Lemma heap_mapsto_own_state_to_mt l v E β:
    ↑mtN ⊆ E → l ↦[β] v ={E}=∗ ∃ q, ⌜β = Own → q = 1%Qp⌝ ∗ l ↦{q} v.
  Proof.
    iIntros (?) "Hl".
    destruct β; simpl; eauto with iFrame.
    iInduction v as [|b v] "IH" forall (l). {
      iExists 1%Qp. iModIntro; iSplit => //.
      rewrite heap_mapsto_nil. iDestruct "Hl" as "[$ _]".
   }
    iDestruct "Hl" as "(#Hb&Hl&Hv)". rewrite shift_loc_0.
    setoid_rewrite shift_loc_S.
    iInv "Hl" as (q1) ">[H1 H2]". iModIntro.
    iSplitL "H1"; first by iExists _; iFrame.
    iMod ("IH" $! (l +ₗ 1%nat) with "[Hb Hv]") as (q2 _) "Hl".
    { iFrame. simpl. assert (S (length v) = 1 + length v)%nat as -> by lia.
      iDestruct (loc_in_bounds_split with "Hb") as "[_ $]". }
    have [q [q1' [q2' [-> ->]]]]:= Qp_lower_bound (q1 / 2) q2.
    iDestruct "H2" as "[H2 _]". iDestruct "Hl" as "[Hl _]".
    iExists q. rewrite (heap_mapsto_cons _ b v). by iFrame.
  Qed.

  Lemma heap_mapsto_own_state_from_mt l v E β q:
    (β = Own → q = 1%Qp) → l ↦{q} v ={E}=∗ l ↦[β] v.
  Proof.
    iIntros (Hb) "Hl" => /=.
    destruct β => /=; first by rewrite Hb.
    iDestruct (heap_mapsto_loc_in_bounds with "Hl") as "#Hin". iFrame "Hin". iClear "Hin".
    iInduction v as [|b v] "IH" forall (l) => //=.
    rewrite heap_mapsto_cons /=. iDestruct "Hl" as "[Hl1 Hl2]".
    iMod ("IH" with "Hl2") as "Hl".
    setoid_rewrite shift_loc_assoc.
    have Hi :∀ i : nat, 1%Z + i = S i by lia. setoid_rewrite Hi. iFrame.
    iApply inv_alloc. iModIntro. rewrite shift_loc_0. iExists _. iFrame.
  Qed.

  Lemma heap_mapsto_own_state_alloc l β v :
    length v ≠ 0%nat →
    l ↦[β] v -∗ alloc_alive_loc l.
  Proof.
    iIntros (?) "Hl".
    destruct β; [ by iApply heap_mapsto_alive|].
    iApply heap_mapsto_alive_strong.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (? ?) "?"; [done|].
    iApply fupd_mask_intro; [done|]. iIntros "_". iExists _, _. by iFrame.
  Qed.

  Lemma heap_mapsto_own_state_share l v E:
    l ↦[Own] v ={E}=∗ l ↦[Shr] v.
  Proof. by apply heap_mapsto_own_state_from_mt. Qed.

  Lemma heap_mapsto_own_state_exist_share l ly E:
    l ↦[Own]|ly| ={E}=∗ l ↦[Shr]|ly|.
  Proof.
    iDestruct 1 as (v ? Hv) "Hl". iMod (heap_mapsto_own_state_share with "Hl").
    iExists _. by iFrame.
  Qed.

  Lemma heap_mapsto_own_state_app l v1 v2 β:
    l ↦[β] (v1 ++ v2) ⊣⊢ l ↦[β] v1 ∗ (l +ₗ length v1) ↦[β] v2.
  Proof.
    destruct β; rewrite /= ?heap_mapsto_app //.
    rewrite big_sepL_app app_length -loc_in_bounds_split.
    setoid_rewrite shift_loc_assoc_nat.
    iSplit; iIntros "[[??][??]]"; iFrame.
  Qed.

  Lemma heap_mapsto_own_state_layout_alt l β ly:
    l ↦[β]|ly| ⊣⊢ ⌜l `has_layout_loc` ly⌝ ∗ ∃ v, ⌜v `has_layout_val` ly⌝ ∗ l↦[β] v.
  Proof. iSplit; iDestruct 1 as (???) "?"; eauto with iFrame. iExists _. by iFrame. Qed.
End own_state.

(** [memcast_compat_type] describes how a type can transfered via a
mem_cast (see also [ty_memcast_compat] below):
- MCNone: The type cannot be transferred across a mem_cast.
- MCCopy: The value type can be transferred to a mem_casted value.
- MCId: mem_cast on a value of this type is the identity.

MCId implies the other two and MCCopy implies MCNone.
  *)
Inductive memcast_compat_type : Set :=
| MCNone | MCCopy | MCId.

Record type `{!typeG Σ} := {
  (** ty_has_op_type should be written such that it computes well and can be solved by solve_goal.
   Also ty_has_op_type should be defined for UntypedOp. *)
  (* TODO: add
   ty_has_op_type ot mt → ty_has_op_type (UntypedOp (ot_layout ot)) mt
   This property is never used explicitly, but relied on by some typing rules *)
  ty_has_op_type : op_type → memcast_compat_type → Prop;
  ty_own : own_state → loc → iProp Σ;
  ty_own_val : val → iProp Σ;
  (* TODO: figure out the right mask here. We cannot give the full
  mask because of sharing for guarded (for similar reasons as in
  rustbelt)*)
  ty_share l E : ↑shrN ⊆ E → ty_own Own l ={E}=∗ ty_own Shr l;
  ty_shr_pers l : Persistent (ty_own Shr l);
  ty_aligned ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ ⌜l `has_layout_loc` ot_layout ot⌝;
  ty_size_eq ot mt v : ty_has_op_type ot mt → ty_own_val v -∗ ⌜v `has_layout_val` ot_layout ot⌝;
  ty_deref ot mt l : ty_has_op_type ot mt → ty_own Own l -∗ l↦: ty_own_val;
  ty_ref ot mt l v : ty_has_op_type ot mt → ⌜l `has_layout_loc` ot_layout ot⌝ -∗ l↦v -∗ ty_own_val v -∗ ty_own Own l;
  ty_memcast_compat v ot mt st:
    ty_has_op_type ot mt →
    ty_own_val v -∗
    match mt with
    | MCNone => True
    | MCCopy => ty_own_val (mem_cast v ot st)
    | MCId => ⌜mem_cast_id v ot⌝
    end;
}.
Arguments ty_own : simpl never.
Arguments ty_has_op_type {_ _} _.
Arguments ty_own_val {_ _} _ : simpl never.
Global Existing Instance ty_shr_pers.

Section memcast.
  Context `{!typeG Σ}.

  Lemma ty_memcast_compat_copy v ot ty st:
    ty.(ty_has_op_type) ot MCCopy →
    ty.(ty_own_val) v -∗ ty.(ty_own_val) (mem_cast v ot st).
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCCopy). Qed.

  Lemma ty_memcast_compat_id v ot ty:
    ty.(ty_has_op_type) ot MCId →
    ty.(ty_own_val) v -∗ ⌜mem_cast_id v ot⌝.
  Proof. move => ?. by apply: (ty_memcast_compat _ _ _ MCId inhabitant). Qed.

  Lemma mem_cast_compat_id (P : val → iProp Σ) v ot st mt:
    (P v ⊢ ⌜mem_cast_id v ot⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof. iIntros (HP) "HP". iDestruct (HP with "HP") as %Hm. rewrite Hm. by destruct mt. Qed.

  Lemma mem_cast_compat_Untyped (P : val → iProp Σ) v ot st mt:
    ((if ot is UntypedOp _ then False else True) → P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end) →
    P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end.
  Proof. move => Hot. destruct ot; try by apply: Hot. apply: mem_cast_compat_id. by iIntros "?". Qed.

  (* It is important this this computes well so that it can be solved automatically. *)
  Definition is_int_ot (ot : op_type) (it : int_type) : Prop:=
    match ot with | IntOp it' => it = it' | UntypedOp ly => ly = it_layout it | _ => False end.
  Definition is_ptr_ot (ot : op_type) : Prop:=
    match ot with | PtrOp => True | UntypedOp ly => ly = void* | _ => False end.
  Definition is_value_ot (ot : op_type) (ot' : op_type) :=
    if ot' is UntypedOp ly then ly = ot_layout ot else ot' = ot.

  Lemma is_int_ot_layout it ot:
    is_int_ot ot it → ot_layout ot = it.
  Proof. by destruct ot => //= ->. Qed.

  Lemma is_ptr_ot_layout ot:
    is_ptr_ot ot → ot_layout ot = void*.
  Proof. by destruct ot => //= ->. Qed.

  Lemma is_value_ot_layout ot ot':
    is_value_ot ot ot' → ot_layout ot' = ot_layout ot.
  Proof. by destruct ot' => //= <-. Qed.

  Lemma mem_cast_compat_int (P : val → iProp Σ) v ot st mt it:
    is_int_ot ot it →
    (P v ⊢ ⌜∃ z, val_to_Z v it = Some z⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof.
    move => ? HT. apply: mem_cast_compat_Untyped => ?.
    apply: mem_cast_compat_id. destruct ot => //; simplify_eq/=.
    etrans; [done|]. iPureIntro => -[??]. by apply: mem_cast_id_int.
  Qed.

  Lemma mem_cast_compat_loc (P : val → iProp Σ) v ot st mt:
    is_ptr_ot ot →
    (P v ⊢ ⌜∃ l, v = val_of_loc l⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof.
    move => ? HT. apply: mem_cast_compat_Untyped => ?.
    apply: mem_cast_compat_id. destruct ot => //; simplify_eq/=.
    etrans; [done|]. iPureIntro => -[? ->]. by apply: mem_cast_id_loc.
  Qed.
End memcast.

Class Copyable `{!typeG Σ} (ty : type) := {
  copy_own_persistent v : Persistent (ty.(ty_own_val) v);
  copy_shr_acc E ot l :
    mtE ⊆ E → ty.(ty_has_op_type) ot MCCopy →
    ty.(ty_own) Shr l ={E}=∗ ⌜l `has_layout_loc` ot_layout ot⌝ ∗
       (* TODO: the closing conjuct does not make much sense with True *)
       ∃ q' vl, l ↦{q'} vl ∗ ▷ ty.(ty_own_val) vl ∗ (▷l ↦{q'} vl ={E}=∗ True)
}.
Global Existing Instance copy_own_persistent.

Class LocInBounds `{!typeG Σ} (ty : type) (β : own_state) (n : nat) := {
  loc_in_bounds_in_bounds l : ty.(ty_own) β l -∗ loc_in_bounds l n
}.
Arguments loc_in_bounds_in_bounds {_ _} _ _ _ {_} _.
Global Hint Mode LocInBounds + + + + - : typeclass_instances.

Section loc_in_bounds.
  Context `{!typeG Σ}.

  Lemma movable_loc_in_bounds ty l ot mt:
    ty.(ty_has_op_type) ot mt →
    ty.(ty_own) Own l -∗ loc_in_bounds l (ly_size (ot_layout ot)).
  Proof.
    iIntros (?) "Hl". iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %<-; [done|]. by iApply heap_mapsto_loc_in_bounds.
  Qed.

  Global Instance intro_persistent_loc_in_bounds l n:
    IntroPersistent (loc_in_bounds l n) (loc_in_bounds l n).
  Proof. constructor. by iIntros "#H !>". Qed.
End loc_in_bounds.

Class AllocAlive `{!typeG Σ} (ty : type) (β : own_state) (P : iProp Σ) := {
  alloc_alive_alive l : P -∗ ty.(ty_own) β l -∗ alloc_alive_loc l
}.
Arguments alloc_alive_alive {_ _} _ _ _ {_} _.
Global Hint Mode AllocAlive + + + + - : typeclass_instances.

Definition type_alive `{!typeG Σ} (ty : type) (β : own_state) : iProp Σ :=
  □ (∀ l, ty.(ty_own) β l -∗ alloc_alive_loc l).
Notation type_alive_own ty := (type_alive ty Own).

Section alloc_alive.
  Context `{!typeG Σ}.

  Lemma movable_alloc_alive ty l ot mt :
    (ot_layout ot).(ly_size) ≠ 0%nat →
    ty.(ty_has_op_type) ot mt →
    ty.(ty_own) Own l -∗ alloc_alive_loc l.
  Proof.
    iIntros (??) "Hl". iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
    iDestruct (ty_size_eq with "Hv") as %Hv; [done|].
    iApply heap_mapsto_alive => //. by rewrite Hv.
  Qed.

  Global Instance intro_persistent_alloc_global l:
    IntroPersistent (alloc_global l) (alloc_global l).
  Proof. constructor. by iIntros "#H !>". Qed.

  Global Instance intro_persistent_type_alive ty β:
    IntroPersistent (type_alive ty β) (type_alive ty β).
  Proof. constructor. by iIntros "#H !>". Qed.

  Global Instance AllocAlive_simpl_and ty β P P' `{!AllocAlive ty β P'} `{!IsProtected P} :
    SimplAndUnsafe true (AllocAlive ty β P) (λ T, P = P' ∧ T).
  Proof. by move => T [-> ?]. Qed.
End alloc_alive.

Typeclasses Opaque type_alive.

Notation "l ◁ₗ{ β } ty" := (ty_own ty β l) (at level 15, format "l  ◁ₗ{ β }  ty") : bi_scope.
Notation "l ◁ₗ ty" := (ty_own ty Own l) (at level 15) : bi_scope.
Notation "v ◁ᵥ ty" := (ty_own_val ty v) (at level 15) : bi_scope.

Declare Scope printing_sugar.
Notation "'frac' { β } l ∶ ty" := (ty_own ty β l) (at level 100, only printing) : printing_sugar.
Notation "'own' l ∶ ty" := (ty_own ty Own l) (at level 100, only printing) : printing_sugar.
Notation "'shr' l ∶ ty" := (ty_own ty Shr l) (at level 100, only printing) : printing_sugar.
Notation "v ∶ ty" := (ty_own_val ty v) (at level 200, only printing) : printing_sugar.

(*** tytrue *)
Section true.
  Context `{!typeG Σ}.
  (** tytrue is a dummy type that all values and locations have. *)
  Program Definition tytrue : type := {|
    ty_own _ _ := True%I;
    ty_has_op_type _ _ := False;
    ty_own_val _ := True%I;
  |}.
  Solve Obligations with try done.
  Next Obligation. iIntros (???) "?". done. Qed.
End true.
(*** refinement types *)
Record rtype `{!typeG Σ} := RType {
  rty_type : Type;
  rty : rty_type → type;
}.
Arguments RType {_ _ _} _.
Add Printing Constructor rtype.

Bind Scope bi_scope with type.
Bind Scope bi_scope with rtype.

Definition with_refinement `{!typeG Σ} (r : rtype) (x : r.(rty_type)) : type := r.(rty) x.
Notation "x @ r" := (with_refinement r x) (at level 14) : bi_scope.
Arguments with_refinement : simpl never.

Program Definition ty_of_rty `{!typeG Σ} (r : rtype) : type := {|
  ty_own q l := (∃ x, (x @ r).(ty_own) q l)%I;
  ty_has_op_type ot mt := ∀ x, (x @ r).(ty_has_op_type) ot mt;
  ty_own_val v := (∃ x, (x @ r).(ty_own_val) v)%I;
|}.
Next Obligation. iDestruct 1 as (?) "H". iExists _. by iMod (ty_share with "H") as "$". Qed.
Next Obligation.
  iIntros (Σ ? r β mt Hly). iDestruct 1 as (x) "Hv". by iDestruct (ty_aligned with "Hv") as %Hv; [done|].
Qed.
Next Obligation.
  iIntros (Σ ? r ot mt v Hly). iDestruct 1 as (x) "Hv". by iDestruct (ty_size_eq with "Hv") as %Hv.
Qed.
Next Obligation.
  iIntros (Σ ? r ot mt l Hly). iDestruct 1 as (x) "Hl".
  iDestruct (ty_deref with "Hl") as (v) "[Hl Hv]"; [done|].
  eauto with iFrame.
Qed.
Next Obligation.
  iIntros (Σ ? r ot mt l v Hly ?) "Hl". iDestruct 1 as (x) "Hv".
  iDestruct (ty_ref with "[] Hl Hv") as "Hl"; [done..|].
  iExists _. iFrame.
Qed.
Next Obligation.
  iIntros (Σ ? r v ot mt st Hot) "[%x Hv]".
  iDestruct (ty_memcast_compat with "Hv") as "?"; [done|].
  case_match => //. iExists _. iFrame.
Qed.

Coercion ty_of_rty : rtype >-> type.
(* TODO: somehow this instance does not work*)
(* Global Instance assume_inj_with_refinement `{!typeG Σ} ty : AssumeInj (=) (=) (with_refinement ty). *)
(* Proof. done. Qed. *)

(* TODO: remove the following? *)
(* Record refined `{!typeG Σ} := { *)
(*   r_type : Type; *)
(*   r_rty : rtype; *)
(*   r_fn : r_type → r_rty.(rty_type); *)
(* }. *)
(* Program Definition rty_of_refined `{!typeG Σ} (r : refined) : rtype := {| *)
(*   rty_type := r.(r_type); *)
(*   rty x := r.(r_rty).(rty) (r.(r_fn) x) *)
(* |}. *)
(* Coercion rty_of_refined : refined >-> rtype. *)

Section rmovable.
  Context `{!typeG Σ}.

  Global Program Instance copyable_ty_of_rty r `{!∀ x, Copyable (x @ r)} : Copyable r.
  Next Obligation.
    iIntros (r ? E ly l ??). iDestruct 1 as (x) "Hl".
    iMod (copy_shr_acc with "Hl") as (? q' vl) "(?&?&?)" => //.
    iSplitR => //. iExists _, _. iFrame. by iExists _.
  Qed.
End rmovable.

Notation "l `at_type` ty" := (with_refinement ty <$> l) (at level 50) : bi_scope.
(* Must be an Hint Extern instead of an Instance since simple apply is not able to apply the instance. *)
Global Hint Extern 1 (AssumeInj (=) (=) (with_refinement _)) => exact: I : typeclass_instances.

(*** Cofe and Ofe *)
Section ofe.
  Context `{!typeG Σ}.

  Inductive type_equiv' (ty1 ty2 : type) : Prop :=
    Type_equiv :
      (∀ ot mt, ty1.(ty_has_op_type) ot mt ↔ ty2.(ty_has_op_type) ot mt) →
      (∀ β l, ty1.(ty_own) β l ≡ ty2.(ty_own) β l) →
      (∀ v, ty1.(ty_own_val) v ≡ ty2.(ty_own_val) v) →
      type_equiv' ty1 ty2.
  Instance type_equiv : Equiv type := type_equiv'.
  Inductive type_dist' (n : nat) (ty1 ty2 : type) : Prop :=
    Type_dist :
      (∀ ot mt, ty1.(ty_has_op_type) ot mt ↔ ty2.(ty_has_op_type) ot mt) →
      (∀ β l, (l ◁ₗ{β} ty1)%I ≡{n}≡ (l ◁ₗ{β} ty2)%I) →
      (∀ v, ty1.(ty_own_val) v ≡{n}≡ ty2.(ty_own_val) v) →
      type_dist' n ty1 ty2.
  Instance type_dist : Dist type := type_dist'.

  Let T := prodO (prodO
    (op_type -d> memcast_compat_type -d> PropO)
    (own_state -d> loc -d> iPropO Σ))
    (val -d> iPropO Σ)
  .
  Let P (x : T) : Prop :=
    (∀ l, Persistent (x.1.2 Shr l)) ∧
    (∀ l E, ↑shrN ⊆ E → x.1.2 Own l ={E}=∗ x.1.2 Shr l) ∧
    (∀ ot mt l, x.1.1 ot mt → x.1.2 Own l -∗ ⌜l `has_layout_loc` ot_layout ot⌝) ∧
    (∀ ot mt v, x.1.1 ot mt → x.2 v -∗ ⌜v `has_layout_val` ot_layout ot⌝) ∧
    (∀ ot mt l, x.1.1 ot mt → x.1.2 Own l -∗ l↦: x.2) ∧
    (∀ ot mt l v, x.1.1 ot mt → ⌜l `has_layout_loc` ot_layout ot⌝ -∗ l↦v -∗ x.2 v -∗ x.1.2 Own l) ∧
    (∀ v ot mt st, x.1.1 ot mt →
    x.2 v -∗
    match mt with
    | MCNone => True
    | MCCopy => x.2 (mem_cast v ot st)
    | MCId => ⌜mem_cast_id v ot⌝
    end).

  Definition type_unpack (ty : type) : T :=
    (λ ot mt, ty.(ty_has_op_type) ot mt, λ β l, (ty.(ty_own) β l), λ v, (ty.(ty_own_val) v)).
  Program Definition type_pack (x : T) (H : P x) : type :=
    {| ty_has_op_type := x.1.1; ty_own := x.1.2; ty_own_val := x.2 |}.
  Solve Obligations with by intros ? (?&?&?&?&?&?&?).

  Definition type_ofe_mixin : OfeMixin type.
  Proof.
    apply (iso_ofe_mixin type_unpack).
    - split; [ by destruct 1|]. by intros [[??]?]; constructor.
    - split; [ by destruct 1|]. by intros [[??]?]; constructor.
  Qed.
  Canonical Structure typeO : ofe := Ofe type type_ofe_mixin.

  Global Instance ty_own_ne n:
    Proper (dist n ==> eq ==> eq ==> dist n) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_own_proper : Proper ((≡) ==> eq ==> eq ==> (≡)) ty_own.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Lemma ty_own_entails `{!typeG Σ} ty1 ty2 β l:
    ty1 ≡@{type} ty2 →
    ty_own ty1 β l -∗ ty_own ty2 β l.
  Proof. by move => [? -> ?]. Qed.

  Global Instance ty_own_val_ne n:
    Proper (dist n ==> eq ==> dist n) ty_own_val.
  Proof. intros ?? EQ ??->. apply EQ. Qed.
  Global Instance ty_own_val_proper : Proper ((≡) ==> eq ==> (≡)) ty_own_val.
  Proof. intros ?? EQ ??->. apply EQ. Qed.
  Global Instance ty_has_op_type_ne n:
    Proper (dist n ==> eq ==> eq ==> iff) ty_has_op_type.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.
  Global Instance ty_has_op_type_proper:
    Proper ((≡) ==> eq ==> eq ==> iff) ty_has_op_type.
  Proof. intros ?? EQ ??-> ??->. apply EQ. Qed.

  Global Instance type_cofe : Cofe typeO.
  Proof.
    apply (iso_cofe_subtype' P type_pack type_unpack).
    - by intros [].
    - split; [ by destruct 1|]. by intros [[??]?]; constructor.
    - by intros.
    - repeat apply limit_preserving_and; repeat (apply limit_preserving_forall; intros ?).
      all: try (apply limit_preserving_impl; [ move => ?? [[Hmt ?]?]; rewrite /impl; by apply Hmt|]).
      all: apply bi.limit_preserving_entails=> n ty1 ty2 [[??]?]; repeat f_equiv.
  Qed.

  Import EqNotations.
  Lemma ty_of_rty_ne rty1 rty2 n (Heq : rty1.(rty_type) = rty2.(rty_type)) :
    (∀ x, (x @ rty1)%I ≡{n}≡ ((rew [λ x : Type, x] Heq in x) @ rty2)%I) →
    ty_of_rty rty1 ≡{n}≡ ty_of_rty rty2.
  Proof.
    destruct rty1, rty2; simpl in *. destruct Heq => /=. rewrite /with_refinement/=.
    move => Hne. constructor => /=.
    - move => ??. apply forall_proper => ?. apply Hne.
    - move => ??. rewrite /ty_own/=. f_equiv => ?. apply Hne.
    - move => ?. rewrite /ty_own_val/=. f_equiv => ?. apply Hne.
  Qed.
  Lemma ty_of_rty_proper rty1 rty2 (Heq : rty1.(rty_type) = rty2.(rty_type)) :
    (∀ x, (x @ rty1)%I ≡ ((rew [λ x : Type, x] Heq in x) @ rty2)%I) →
    ty_of_rty rty1 ≡ ty_of_rty rty2.
  Proof.
    destruct rty1, rty2; simpl in *. destruct Heq => /=. rewrite /with_refinement/=.
    move => Hne. constructor => /=.
    - move => ??. apply forall_proper => ?. apply Hne.
    - move => ??. rewrite /ty_own/=. f_equiv => ?. apply Hne.
    - move => ?. rewrite /ty_own_val/=. f_equiv => ?. apply Hne.
  Qed.

  (* Inductive rtype_equiv' (ty1 ty2 : rtype) : Prop := *)
  (*   RType_equiv (H : ty1.(rty_type) = ty2.(rty_type)): *)
  (*     ((eq_rect _ (λ x, x -d> _) ty1.(rty) _ H) ≡ ty2.(rty)) → *)
  (*     rtype_equiv' ty1 ty2. *)
  (* Instance rtype_equiv : Equiv rtype := rtype_equiv'. *)
  (* Inductive rtype_dist' (n : nat) (ty1 ty2 : rtype) : Prop := *)
  (*   RType_dist (H : ty1.(rty_type) = ty2.(rty_type)): *)
  (*     ((eq_rect _ (λ x, x -d> _) ty1.(rty) _ H) ≡{n}≡ ty2.(rty)) → *)
  (*     rtype_dist' n ty1 ty2. *)
  (* Instance rtype_dist : Dist rtype := rtype_dist'. *)

  (* Let RT := (sigT (λ x, x -d> typeO)). *)
  (* Let RP (x : RT) : Prop := True. *)

  (* Definition rtype_unpack (ty : rtype) : RT := *)
  (*   (existT _ ty.(rty)). *)
  (* Program Definition rtype_pack (x : RT) (H : RP x) : rtype := *)
  (*   {| rty := projT2 x |}. *)

  (* Global Instance proof_irrel_axiom : ∀ a b : Type, ProofIrrel (a = b). *)
  (* Admitted. *)

  (* Definition rtype_ofe_mixin : OfeMixin rtype. *)
  (* Proof. *)
  (*   apply (iso_ofe_mixin rtype_unpack). *)
  (*   - split. *)
  (*     + destruct 1. apply sigT_equiv_eq_alt. eauto. *)
  (*     + move => /sigT_equiv_eq_alt/= [H1 H2]. by econstructor. *)
  (*   - split. *)
  (*     + destruct 1. eexists _. eauto. *)
  (*     + destruct 1. by econstructor. *)
  (* Qed. *)
  (* Canonical Structure rtypeO : ofe := Ofe rtype rtype_ofe_mixin. *)


  (* Global Instance with_refinement_ne n: *)
  (*   Proper (dist n ==> eq ==> dist n) with_refinement. *)
  (* Proof. intros ?? EQ ??-> ??->. apply EQ. Qed. *)

  Global Instance type_equivalence : Equivalence (≡@{type}).
  Proof.
    constructor.
    - done.
    - move => ?? [???]. constructor => *; by symmetry.
    - move => ??? [???] [???].
      constructor => *; (etrans; [match goal with | H : _ |- _ => apply H end|]; done).
  Qed.
End ofe.

Ltac simpl_type :=
  simpl;
  repeat match goal with
        | |- context C [ty_own {| ty_own := ?f |}] => let G := context C [f] in change G
        | |- context C [ty_own_val {| ty_own_val := ?f |}] => let G := context C [f] in change G
        | |- context C [ty_own (?x @ {| rty := ?f |})] =>
            let G := context C [let '({| ty_own := y |}) := (f x) in y ] in
            change G
        | |- context C [ty_own_val (?x @ {| rty := ?f |})] =>
            let G := context C [let '({| ty_own_val := y |}) := (f x) in y ] in
            change G
     end; simpl.

Ltac unfold_type_equiv :=
  lazymatch goal with
  | |- (_ <$> _)%I ≡{_}≡ (_ <$> _)%I => apply list.list_fmap_ext_ne; intros
  | |- (?a @ ?ty1)%I ≡{?n}≡ (?b @ ?ty2)%I => change (rty ty1 a ≡{n}≡ rty ty2 b); simpl
  | |- (?a @ ?ty1)%I ≡ (?b @ ?ty2)%I => change (rty ty1 a ≡ rty ty2 b); simpl
  | |- ty_of_rty _ ≡{?n}≡ ty_of_rty _ => simple refine (ty_of_rty_ne _ _ _ _ _) => /=; [exact: eq_refl|] => ? /=
  | |- ty_of_rty _ ≡ ty_of_rty _ => simple refine (ty_of_rty_proper _ _ _ _) => /=; [exact: eq_refl|] => ? /=
  | |- {| ty_own := _ |} ≡{?n}≡ {| ty_own := _ |} =>
      constructor => *; simpl_type
  | |- {| ty_own := ?f1 |} ≡ {| ty_own := ?f2 |} =>
      constructor => *; simpl_type
   | H : ?x ≡{_}≡ _ |- ty_has_op_type ?x _ _ ↔ _ => apply H
   | H : ?x ≡ _ |- ty_has_op_type ?x _ _ ↔ _ => apply H
  | |- context [let '_ := ?x in _] => destruct x
  end.

(* A version of f_equiv which performs better for the kinds of goals
we see in this development (e.g. mpool_spec). *)
Ltac f_equiv' :=
  match goal with
  | |- pointwise_relation _ _ _ _ => intros ?
  | |- prod_relation _ _ ?p _ => is_var p; destruct p
  (* We support matches on both sides, *if* they concern the same variable, or *)
     (* variables in some relation. *)
  | |- ?R (match ?x with _ => _ end) (match ?x with _ => _ end) =>
    destruct x
  | H : ?R ?x ?y |- ?R2 (match ?x with _ => _ end) (match ?y with _ => _ end) =>
     destruct H
  | |- _ = _ => reflexivity

  | |- ?R (?f _) _ => simple apply (_ : Proper (R ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (R ==> R ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (R ==> R ==> R ==> R ==> R) f)
  | |- ?R (?f _ _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _ _) _ => simple apply (_ : Proper (_ ==> _ ==> _ ==> R) f)
  | |- ?R (?f _ _) _ => simple apply (_ : Proper (_ ==> _ ==> R) f)
  | |- ?R (?f _) _ => simple apply (_ : Proper (_ ==> R) f)
  (* In case the function symbol differs, but the arguments are the same, *)
     (* maybe we have a pointwise_relation in our context. *)
  (* TODO: If only some of the arguments are the same, we could also *)
  (*    query for "pointwise_relation"'s. But that leads to a combinatorial *)
  (*    explosion about which arguments are and which are not the same. *)
  | H : pointwise_relation _ ?R ?f ?g |- ?R (?f ?x) (?g ?x) => simple apply H
  | H : pointwise_relation _ (pointwise_relation _ ?R) ?f ?g |- ?R (?f ?x ?y) (?g ?x ?y) => simple apply H
  end.

Ltac solve_type_proper :=
  solve_proper_core ltac:(fun _ => first [ fast_reflexivity | unfold_type_equiv | f_contractive | f_equiv' | reflexivity ]).
(* for debugging use
   solve_proper_prepare.
   first [ eassumption | fast_reflexivity | unfold_type_equiv | f_contractive | f_equiv' | reflexivity ].
*)


(*** Tests *)
Section tests.
  Context `{!typeG Σ}.

  Example binding l (r : Z → rtype) v x T : True -∗ l ◁ₗ x @ r v ∗ T. Abort.

End tests.
