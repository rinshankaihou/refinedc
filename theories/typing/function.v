From refinedc.typing Require Export type.
From refinedc.typing Require Import programs uninit.
Set Default Proof Using "Type".

Section function.
  Context `{!typeG Σ} {A : Type}.

  Record fn_params := FP {
    fp_atys : list mtype;
    fp_Pa : iProp Σ;
    fp_rtype : Type;
    fp_fr: fp_rtype → fn_ret;
  }.

  Definition FP_wf {B} (atys : list type) `{!MovableLst atys} (Pa : iProp Σ) (fr : B → fn_ret)  :=
    FP (movablelst_to_list atys) Pa B fr.

  Definition typed_function (fn : function) (fp : A → fn_params) : iProp Σ :=
    (∀ x, ⌜Forall2 (λ (ty : mtype) '(_, p), ty.(ty_layout) = p) (fp x).(fp_atys) (f_args fn)⌝ ∗
      □ ∀ (lsa : vec loc (length (fp x).(fp_atys))) (lsv : vec loc (length fn.(f_local_vars))),
          let Qinit := ([∗list] l;t∈lsa;(fp x).(fp_atys), l ◁ₗ (t:mtype)) ∗
                       ([∗list] l;p∈lsv;fn.(f_local_vars), l ◁ₗ uninit (p.2)) ∗ (fp x).(fp_Pa) in
          let Q := (subst_stmt (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> (lsa ++ lsv))) <$> fn.(f_code) in
          Qinit -∗ typed_stmt (Goto fn.(f_init)) fn (lsa ++ lsv) (fp x).(fp_fr) Q
    )%I.

  Global Instance typed_function_persistent fn fp : Persistent (typed_function fn fp) := _.

  Program Definition function_ptr (fp : A → fn_params) : rtype := {|
    rty_type := loc;
    rty f := {|
      ty_own β l := (∃ fn, ⌜l `has_layout_loc` LPtr⌝ ∗ l ↦[β] val_of_loc f ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
  |} |}.
  Next Obligation. iDestruct 1 as (fn) "[? [H [? ?]]]". iExists _. iFrame. by iApply heap_mapsto_own_state_share. Qed.

  Global Program Instance rmovable_function_ptr fp : RMovable (function_ptr fp) := {|
    rmovable f := {|
      ty_layout := LPtr;
      ty_own_val v := (∃ fn, ⌜v = val_of_loc f⌝  ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
  |} |}.
  Next Obligation. iIntros (? f l). by iDestruct 1 as (??) "?". Qed.
  Next Obligation. iIntros (f v ?). by iDestruct 1 as (? ->) "?". Qed.
  Next Obligation. iIntros (f v ?). iDestruct 1 as (??) "(?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (f v ???) "?". iDestruct 1 as (? ->) "?". iFrame. iExists _. by iFrame. Qed.
  Next Obligation. by iIntros (f v). Qed.

  Definition typed_callable (v : val) (ty : type) `{!Movable ty} (T : (A → fn_params) → iProp Σ) : iProp Σ :=
    (v ◁ᵥ ty -∗ ∃ f fn fp, ⌜v = val_of_loc f⌝ ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp ∗ T fp)%I.

  Lemma type_callable l v T fp:
    T fp -∗ typed_callable v (l @ function_ptr fp) T.
  Proof.
    iIntros "HT Hv".
    iDestruct "Hv" as (fn ->) "[? ?]".
    iExists _,_,_. by iFrame.
  Qed.


  Lemma type_call {B} r ef es s Q fn' ls (fr : B → _):
    typed_val_expr ef (λ vf tyf,
      typed_callable vf tyf (λ fp,
        (* we need to write this lemma in this funky style to ensure
         that ∃ x, is after we have evaluated the expressions since
         thie evaluation might destruct exististential quantifiers
         which we want to use to instantiate x *)
        foldr (λ e T vl, typed_val_expr e (λ v ty,
             v ◁ᵥ ty -∗ T (vl ++ [v])))
              (λ vl, ∃ x,
                  ([∗ list] v;ty∈vl; (fp x).(fp_atys), v ◁ᵥ (ty : mtype)) ∗
                  (fp x).(fp_Pa) ∗ ∀ v x',
                  v ◁ᵥ ((fp x).(fp_fr) x').(fr_rty) -∗ ((fp x).(fp_fr) x').(fr_R)  -∗
                   typed_stmt (subst_stmt [r] [v] s) fn' ls fr Q
              )
              es [])) -∗
    typed_stmt (r <- ef with es; s) fn' ls fr Q.
  Proof.
    iIntros "He". iIntros (Hls).
    iApply wps_call_bind. iApply "He". iIntros (vf tyf) "Hvf He".
    iDestruct ("He" with "Hvf") as (f fn fp ->) "(#? & Hfn & He)" => /=.
    move: {3 5}[] => vl.
    iInduction es as [|e es] "IH" forall (vl) => /=. 2: {
      iApply "He". iIntros (v ty) "Hv Hnext". iApply ("IH" with "Hfn"). by iApply "Hnext".
    }
    iDestruct "He" as (x) "(Hvl&HPa&Hr)".
    iDestruct ("Hfn" $! x) as "[Hl #Hfn]".
    iApply fupd_wps. iMod "Hl" as %Hl. iModIntro.
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HPa Hr".
      move: Hl. move: (fp_atys (fp x)) => atys Hl.
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl atys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Hvl" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?.
      iPureIntro. constructor => //. by rewrite -Heq.
    }
    iApply (wps_call with "[//]") => //. by apply val_to_of_loc.
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iDestruct (big_sepL2_length with "Ha") as %Hlen1.
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    iDestruct (big_sepL2_length with "Hvl") as %Hlen3.
    have [lsa' ?]: (∃ (ls : vec loc (length (fp_atys (fp x)))), lsa = ls) by rewrite -Hlen3 -Hlen1; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.
    have [lsv' ?]: (∃ (ls : vec loc (length (f_local_vars fn))), lsv = ls) by rewrite -Hlen2; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.

    iDestruct ("Hfn" $! lsa' lsv') as "#Hm". iClear "Hfn".
    iExists _. iSplitR "Hr" => /=.
    - iFrame. iApply ("Hm" with "[-]"). 2:{
        iPureIntro. rewrite !app_length. f_equal => //. rewrite Hlen1 Hlen3. by eapply Forall2_length.
      } iClear "Hm". iFrame.
      move: Hlen1 Hly. move: (lsa' : list _) => lsa'' Hlen1 Hly. clear lsa' Hall.
      move: Hlen3 Hl. move: (fp_atys (fp x)) => atys Hlen3 Hl.
      move: Hly Hl. move: (f_args fn) => alys Hly Hl.
      iInduction (vl) as [|v vl] "IH" forall (atys lsa'' alys Hlen1 Hly Hlen3 Hl). by destruct atys, lsa''.
      destruct atys, lsa'' => //.
      move: Hl => /(Forall2_cons_inv_l _ _)[[??][?[?[??]]]]; simplify_eq. csimpl in *.
      move: Hly => /(Forall2_cons_inv _ _ _ _)[??].
      iDestruct "Hvl" as "[Hv ?]".
      iDestruct "Ha" as "[Ha ?]".
      iDestruct (ty_ref with "[] Ha Hv") as "$". done.
      by iApply ("IH" with "[] [] [] [] [$] [$]"); iPureIntro; simplify_eq.
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { rewrite Hlen1 Hlen3. by eapply Forall2_length. }
      iApply fupd_wps.
      by iApply ("Hr" with "Hv HPr").
  Qed.


  Lemma subsume_fnptr v l1 l2 (fnty1 fnty2 : A → fn_params) T:
    ⌜l1 = l2⌝ ∗ ⌜fnty1 = fnty2⌝ ∗ T -∗
    subsume (v ◁ᵥ l1 @ function_ptr fnty1) (v ◁ᵥ l2 @ function_ptr fnty2) T.
  Proof. iIntros "(->&->&$) $". Qed.
  Global Instance subsume_fnptr_inst v l1 l2 (fnty1 fnty2 : A → fn_params):
    Subsume (v ◁ᵥ l1 @ function_ptr fnty1)%I (v ◁ᵥ l2 @ function_ptr fnty2)%I :=
    λ T, i2p (subsume_fnptr v l1 l2 fnty1 fnty2 T).
End function.

Notation "'fn(∀' x ':' A ';' T1 ',' .. ',' TN ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((fun x => FP_wf (B:=B) (@cons type T1%I .. (@cons type TN%I (@nil type)) ..) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  T1 ','  .. ','  TN ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.

Notation "'fn(∀' x ':' A ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((λ x, FP_wf (B:=B) (@nil type) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.


Typeclasses Opaque typed_function.

(*** Tests *)
Section test.
  Context  `{!typeG Σ}.

  Local Definition test_fn := fn(∀ () : (); (uninit size_t); True) → ∃ () : (), void; True.
  Local Definition test_fn2 := fn(∀ () : (); True) → ∃ () : (), void; True.
  Local Definition test_fn3 := fn(∀ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z; uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t; True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True) → ∃ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z, uninit size_t; True%I.

  Goal ∀ (l : loc) fn, l ◁ᵥ l @ function_ptr test_fn2 -∗ typed_function fn test_fn.
  Abort.
End test.
