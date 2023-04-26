From refinedc.typing Require Export type.
From refinedc.typing Require Import programs bytes.
Set Default Proof Using "Type".

Definition introduce_typed_stmt {Σ} `{!typeG Σ} (fn : function) (ls : list loc) (R : val → type → iProp Σ) : iProp Σ :=
  let Q := (subst_stmt (zip (fn.(f_args).*1 ++ fn.(f_local_vars).*1)
                            (val_of_loc <$> ls))) <$> fn.(f_code) in
  typed_stmt (Goto fn.(f_init)) fn ls R Q.
Global Typeclasses Opaque introduce_typed_stmt.
Arguments introduce_typed_stmt : simpl never.

Section function.
  Context `{!typeG Σ} {A : Type}.
  Record fn_ret := FR {
    (* return type (rc::returns) *)
    fr_rty : type;
    (* postcondition (rc::ensures) *)
    fr_R : iProp Σ;
  }.
  Definition mk_FR (rty : type) (R : iProp Σ) := FR rty R.


  (* The specification of a function is given by [A → fn_params].
     The full specification roughly looks like the following:
     ∀ x : A, args ◁ᵥ fp_atys ∗ fp_Pa → ∃ y : fp_rtype, ret ◁ᵥ fr_rty ∗ fr_R
 *)
  Record fn_params := FP {
    (* types of arguments (rc::args) *)
    fp_atys : list type;
    (* precondition (rc::requires) *)
    fp_Pa : iProp Σ;
    (* type of the existential quantifier (rc::exists) *)
    fp_rtype : Type;
    (* return type and postcondition (rc::returns and rc::ensures) *)
    fp_fr: fp_rtype → fn_ret;
  }.

  Definition fn_ret_prop {B} (fr : B → fn_ret) : val → type → iProp Σ :=
    (λ v ty, v ◁ᵥ ty -∗ ∃ x, v ◁ᵥ (fr x).(fr_rty) ∗ (fr x).(fr_R) ∗ True)%I.

  Definition FP_wf {B} (atys : list type) (Pa : iProp Σ) (fr : B → fn_ret)  :=
    FP atys Pa B fr.

  Definition typed_function (fn : function) (fp : A → fn_params) : iProp Σ :=
    (∀ x, ⌜Forall2 (λ (ty : type) '(_, p), ty.(ty_has_op_type) (UntypedOp p) MCNone) (fp x).(fp_atys) (f_args fn)⌝ ∗
      □ ∀ (lsa : vec loc (length (fp x).(fp_atys))) (lsv : vec loc (length fn.(f_local_vars))),
          let Qinit := ([∗list] l;t∈lsa;(fp x).(fp_atys), l ◁ₗ t) ∗
                       ([∗list] l;p∈lsv;fn.(f_local_vars), l ◁ₗ uninit (p.2)) ∗ (fp x).(fp_Pa) in
          Qinit -∗ introduce_typed_stmt fn (lsa ++ lsv) (fn_ret_prop (fp x).(fp_fr))
    )%I.

  Global Instance typed_function_persistent fn fp : Persistent (typed_function fn fp) := _.

  Import EqNotations.
  Lemma typed_function_equiv fn1 fn2 (fp1 fp2 : A → _) :
    fn1 = fn2 →
    (∀ x, Forall2 (λ ty '(_, p), ty_has_op_type ty (UntypedOp p) MCNone) (fp_atys (fp2 x)) (f_args fn2)) →
    (* TODO: replace the following with an equivalenve relation for fn_params? *)
    (∀ x, ∃ Heq : (fp1 x).(fp_rtype) = (fp2 x).(fp_rtype),
          (fp1 x).(fp_atys) ≡ (fp2 x).(fp_atys) ∧
          (fp1 x).(fp_Pa) ≡ (fp2 x).(fp_Pa) ∧
          (∀ y, ((fp1 x).(fp_fr) y).(fr_rty) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_rty) ∧
                ((fp1 x).(fp_fr) y).(fr_R) ≡ ((fp2 x).(fp_fr) (rew [λ x : Type, x] Heq in y)).(fr_R))) →
    typed_function fn1 fp1 -∗ typed_function fn2 fp2.
  Proof.
    iIntros (-> Hly Hfn) "HT".
    rewrite /typed_function.
    iIntros (x). iDestruct ("HT" $! x) as ([Hlen Hall]%Forall2_same_length_lookup) "#HT".
    have [Heq [Hatys [HPa Hret]]] := Hfn x.
    iSplit; [done|].
    rewrite /introduce_typed_stmt.
    iIntros "!>" (lsa lsv) "[Hv Ha] %". rewrite -HPa.
    have [|lsa' Hlsa]:= vec_cast _ lsa (length (fp_atys (fp1 x))). { by rewrite Hatys. }
    iApply (wps_wand with "[Hv Ha]").
    - iSpecialize ("HT" $! lsa' lsv with "[Hv Ha]"); rewrite Hlsa. {
        iFrame. iApply (big_sepL2_impl' with "Hv") => //. 1: by rewrite Hatys.
        move: Hatys => /list_equiv_lookup Hatys.
        iIntros "!>" (k ????? Haty2 ? Haty1) "?".
        have := Hatys k. rewrite Haty1 Haty2=> /(Some_equiv_eq _ _)[?[? [Heql ?]]].
        rewrite -Heql. by simplify_eq.
      }
      iApply "HT". by rewrite -Hlsa.
    - rewrite /typed_stmt_post_cond. iIntros (v).
      iDestruct 1 as (?) "[?[? HR]]". rewrite Hlsa.
      iExists _. iFrame.
      iIntros "Hty". iDestruct ("HR" with "Hty") as (y) "[?[??]]".
      have [-> ->]:= Hret y.
      iExists (rew [λ x : Type, x] Heq in y). iFrame.
  Qed.

  Program Definition function_ptr_type (fp : A → fn_params) (f : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (∃ fn, ⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] val_of_loc f ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
    ty_own_val v := (∃ fn, ⌜v = val_of_loc f⌝  ∗ fntbl_entry f fn ∗ ▷ typed_function fn fp)%I;
  |}.
  Next Obligation. iDestruct 1 as (fn) "[? [H [? ?]]]". iExists _. iFrame. by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (fp f ot mt l ->%is_ptr_ot_layout). by iDestruct 1 as (??) "?". Qed.
  Next Obligation. iIntros (fp f ot mt v ->%is_ptr_ot_layout). by iDestruct 1 as (? ->) "?". Qed.
  Next Obligation. iIntros (fp f ot mt v ?). iDestruct 1 as (??) "(?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (fp f ot mt v ? ->%is_ptr_ot_layout ?) "?". iDestruct 1 as (? ->) "?". iFrame. iExists _. by iFrame. Qed.
  Next Obligation.
    iIntros (fp f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[%fn [-> ?]]". iPureIntro. naive_solver.
  Qed.

  Definition function_ptr (fp : A → fn_params) : rtype :=
    RType (function_ptr_type fp).

  Global Program Instance copyable_function_ptr p fp : Copyable (p @ function_ptr fp).
  Next Obligation.
    iIntros (p fp E ly l ? ->%is_ptr_ot_layout). iDestruct 1 as (fn Hl) "(Hl&?&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit.
    - by iExists _; iFrame.
    - by iIntros "_".
  Qed.

  Lemma type_call_fnptr l v vl tys T fp:
    (([∗ list] v;ty∈vl; tys, v ◁ᵥ ty) -∗ ∃ x,
      ([∗ list] v;ty∈vl; (fp x).(fp_atys), v ◁ᵥ ty) ∗
      (fp x).(fp_Pa) ∗ ∀ v x',
      ((fp x).(fp_fr) x').(fr_R) -∗
      T v ((fp x).(fp_fr) x').(fr_rty)
    ) -∗ typed_call v (v ◁ᵥ l @ function_ptr fp) vl tys T.
  Proof.
    iIntros "HT (%fn&->&He&Hfn) Htys" (Φ) "HΦ".
    iDestruct ("HT" with "Htys") as "(%x&Hvl&HPa&Hr)".
    iDestruct ("Hfn" $! x) as "[>%Hl #Hfn]".
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HPa Hr".
      move: Hl. move: (fp_atys (fp x)) => atys Hl.
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl atys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Hvl" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] He HΦ Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iPureIntro. constructor => //.
    }
    iApply (wp_call with "He") => //. { by apply val_to_of_loc. }
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iDestruct (big_sepL2_length with "Ha") as %Hlen1.
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    iDestruct (big_sepL2_length with "Hvl") as %Hlen3.
    have [lsa' ?]: (∃ (ls : vec loc (length (fp_atys (fp x)))), lsa = ls) by rewrite -Hlen3 -Hlen1; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.
    have [lsv' ?]: (∃ (ls : vec loc (length (f_local_vars fn))), lsv = ls) by rewrite -Hlen2; eexists (list_to_vec _); symmetry; apply vec_to_list_to_vec. subst.

    iDestruct ("Hfn" $! lsa' lsv') as "#Hm". iClear "Hfn". unfold introduce_typed_stmt.
    iExists _. iSplitR "Hr HΦ" => /=.
    - iFrame. iApply ("Hm" with "[-]"). 2:{
        iPureIntro. rewrite !app_length. f_equal => //. rewrite Hlen1 Hlen3. by eapply Forall2_length.
      } iClear "Hm". iFrame.
      move: Hlen1 Hly. move: (lsa' : list _) => lsa'' Hlen1 Hly. clear lsa' Hall.
      move: Hlen3 Hl. move: (fp_atys (fp x)) => atys Hlen3 Hl.
      move: Hly Hl. move: (f_args fn) => alys Hly Hl.
      iInduction (vl) as [|v vl] "IH" forall (atys lsa'' alys Hlen1 Hly Hlen3 Hl).
      { destruct atys, lsa'' => //. iSplitR => //. iApply (big_sepL2_mono with "Hv").
        iIntros (?????) => /=. iDestruct 1 as (??) "[%?]".
        iExists _. iFrame. by rewrite Forall_forall. }
      destruct atys, lsa'' => //.
      move: Hl => /(Forall2_cons_inv_l _ _)[[??][?[?[??]]]]; simplify_eq. csimpl in *.
      move: Hly => /(Forall2_cons _ _ _ _)[??].
      iDestruct "Hvl" as "[Hvl ?]".
      iDestruct "Ha" as "[Ha ?]".
      iDestruct (ty_ref with "[] Ha Hvl") as "$"; [done..|].
      by iApply ("IH" with "[] [] [] [] [$] [$]").
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { rewrite Hlen1 Hlen3. left. by eapply Forall2_length. }
      iDestruct ("HPr" with "Hv") as (?) "[Hty [HR _]]".
      iApply ("HΦ" with "Hty").
      by iApply ("Hr" with "HR").
  Qed.
  Global Instance type_call_fnptr_inst l v vl fp tys :
    TypedCallVal v (l @ function_ptr fp) vl tys :=
    λ T, i2p (type_call_fnptr l v vl tys T fp).

  Lemma subsume_fnptr v l1 l2 (fnty1 fnty2 : A → fn_params) T:
    ⌜l1 = l2⌝ ∗ ⌜fnty1 = fnty2⌝ ∗ T -∗
    subsume (v ◁ᵥ l1 @ function_ptr fnty1) (v ◁ᵥ l2 @ function_ptr fnty2) T.
  Proof. iIntros "(->&->&$) $". Qed.
  Global Instance subsume_fnptr_inst v l1 l2 (fnty1 fnty2 : A → fn_params):
    Subsume (v ◁ᵥ l1 @ function_ptr fnty1)%I (v ◁ᵥ l2 @ function_ptr fnty2)%I :=
    λ T, i2p (subsume_fnptr v l1 l2 fnty1 fnty2 T).
End function.
Arguments fn_ret_prop _ _ _ /.

Notation "'fn(∀' x ':' A ';' T1 ',' .. ',' TN ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((fun x => FP_wf (B:=B) (@cons type T1%I .. (@cons type TN%I (@nil type)) ..) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  T1 ','  .. ','  TN ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.

Notation "'fn(∀' x ':' A ';' Pa ')' '→' '∃' y ':' B ',' rty ';' Pr" :=
  ((λ x, FP_wf (B:=B) (@nil type) Pa%I (λ y, mk_FR rty%I Pr%I)) : A → fn_params)
  (at level 99, Pr at level 200, x pattern, y pattern,
   format "'fn(∀'  x  ':'  A ';' '/'  Pa ')'  '→' '/'  '∃'  y  ':'  B ','  rty  ';'  Pr") : stdpp_scope.


Global Typeclasses Opaque typed_function.
Global Typeclasses Opaque function_ptr_type.

Section inline_function.
  Context `{!typeG Σ} {A : Type}.

  Program Definition inline_function_ptr_type (fn : function) (f : loc) : type := {|
    ty_has_op_type ot mt := is_ptr_ot ot;
    ty_own β l := (⌜l `has_layout_loc` void*⌝ ∗ l ↦[β] val_of_loc f ∗ fntbl_entry f fn)%I;
    ty_own_val v := (⌜v = val_of_loc f⌝ ∗ fntbl_entry f fn)%I;
  |}.
  Next Obligation. iDestruct 1 as "[? [H ?]]". iFrame. by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (fn f ot mt l ->%is_ptr_ot_layout). by iDestruct 1 as (?) "?". Qed.
  Next Obligation. iIntros (fn f ot mt v ->%is_ptr_ot_layout). by iDestruct 1 as (->) "?". Qed.
  Next Obligation. iIntros (fn f ot mt v ?). iDestruct 1 as (?) "(?&?)". eauto with iFrame. Qed.
  Next Obligation. iIntros (fn f ot mt l v ->%is_ptr_ot_layout ?) "?". iDestruct 1 as (->) "?". by iFrame. Qed.
  Next Obligation.
    iIntros (fn f v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed.

  Definition inline_function_ptr (fn : function) : rtype :=
    RType (inline_function_ptr_type fn).

  Global Program Instance copyable_inline_function_ptr p fn : Copyable (p @ inline_function_ptr fn).
  Next Obligation.
    iIntros (p fn E l ly ? ->%is_ptr_ot_layout). iDestruct 1 as (Hl) "(Hl&?)".
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit; [done|].
    by iIntros "_".
  Qed.

  Lemma type_call_inline_fnptr l v vl tys T fn:
    (⌜Forall2 (λ ty '(_, p), ty.(ty_has_op_type) (UntypedOp p) MCNone) tys (f_args fn)⌝ ∗
      foldr (λ '(v, ty) T lsa, ∀ l, l ◁ₗ ty -∗ T (lsa ++ [l]))
      (λ lsa, foldr (λ ly T lsv, ∀ l, l ◁ₗ uninit ly -∗ T (lsv ++ [l]))
                    (λ lsv,
                     introduce_typed_stmt fn (lsa ++ lsv) T)
                    fn.(f_local_vars).*2 [])
      (zip vl tys)
      [])
    -∗ typed_call v (v ◁ᵥ l @ inline_function_ptr fn) vl tys T.
  Proof.
    iIntros "[%Hl HT] (->&Hfn) Htys" (Φ) "HΦ".
    iAssert ⌜Forall2 has_layout_val vl (f_args fn).*2⌝%I as %Hall. {
      iClear "Hfn HT HΦ".
      iInduction (fn.(f_args)) as [|[??]] "IH" forall (vl tys Hl).
      { move: Hl => /Forall2_nil_inv_r ->. destruct vl => //=. }
      move: Hl. intros (?&?&Heq&?&->)%Forall2_cons_inv_r.
      destruct vl => //=. iDestruct "Htys" as "[Hv Hvl]".
      iDestruct ("IH" with "[//] Hvl") as %?.
      iDestruct (ty_size_eq with "Hv") as %?; [done|].
      iPureIntro. constructor => //.
    }
    iApply (wp_call with "Hfn") => //. { by apply val_to_of_loc. }
    iIntros "!#" (lsa lsv Hly) "Ha Hv".
    iAssert ⌜length lsa = length (f_args fn)⌝%I as %Hlen1. {
      iDestruct (big_sepL2_length with "Ha") as %->.
      iPureIntro. move: Hall => /Forall2_length ->. by rewrite fmap_length.
    }
    iDestruct (big_sepL2_length with "Hv") as %Hlen2.
    move: Hl Hall Hly. move: {1 2 3}(f_args fn) => alys Hl Hall Hly.
    have : lsa = [] ++ lsa by done.
    move: {1 5}([]) => lsr.
    move: {1 3 4}(lsa) Hly => lsa' Hly Hr.
    iInduction vl as [|v vl] "IH" forall (tys lsa' alys lsr Hr Hly Hl Hall) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_r with "Ha") as (???) "[Hmt ?]".
       iDestruct (big_sepL2_cons_inv_l with "Htys") as (???) "[Hv' ?]". simplify_eq/=.
       move: Hl => /(Forall2_cons_inv_l _ _ _ _)[[??][?[?[??]]]]. simplify_eq/=.
       move: Hly => /(Forall2_cons _ _ _ _)[??].
       move: Hall => /(Forall2_cons _ _ _ _)[??].
       iDestruct (ty_ref with "[] Hmt Hv'") as "Hl"; [done..|].
       iSpecialize ("HT" with "Hl").
       iApply ("IH" with "[%] [//] [//] [//] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_r with "Ha") as %?. subst.
    move: {1 2}(f_local_vars fn) => vlys.
    have : lsv = [] ++ lsv by done.
    move: {1 3}([]) => lvr.
    move: {2 3}(lsv) => lsv' Hr.
    iInduction lsv' as [|lv lsv'] "IH" forall (vlys lvr Hr) => /=. 2: {
       iDestruct (big_sepL2_cons_inv_l with "Hv") as (???) "[(%x&%&%&Hl) ?]". simplify_eq/=.
       iSpecialize ("HT" $! lv with "[Hl]"). { iExists _. iFrame. iPureIntro. split_and! => //. by apply: Forall_true. }
       iApply ("IH" with "[%] HT [$] [$] [$] [$]").
       by rewrite -app_assoc/=.
    }
    iDestruct (big_sepL2_nil_inv_l with "Hv") as %?. subst.
    simplify_eq/=.
    rewrite /introduce_typed_stmt !right_id_L.
    iExists _. iSplitR "HΦ" => /=.
    - iFrame. iApply ("HT" with "[-]"). iPureIntro. rewrite !app_length -Hlen1 -Hlen2 !app_length/=. lia.
    - iIntros (v). iDestruct 1 as (x') "[Hv [Hls HPr]]".
      iDestruct (big_sepL2_app_inv with "Hls") as "[$ $]".
      { left. by rewrite -Hlen1 right_id_L.  }
      by iApply ("HΦ" with "Hv HPr").
  Qed.
  Global Instance type_call_inline_fnptr_inst l v vl tys fn :
    TypedCallVal v (l @ inline_function_ptr fn) vl tys :=
    λ T, i2p (type_call_inline_fnptr l v vl tys T fn).
End inline_function.

Global Typeclasses Opaque inline_function_ptr_type.

(*** Tests *)
Section test.
  Context  `{!typeG Σ}.

  Local Definition test_fn := fn(∀ () : (); (uninit size_t); True) → ∃ () : (), void; True.
  Local Definition test_fn2 := fn(∀ () : (); True) → ∃ () : (), void; True.
  Local Definition test_fn3 := fn(∀ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z; uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t, uninit size_t; True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True ∗ True) → ∃ (n1, n2, n3, n4, n5, n6, n7) : Z * Z * Z * Z * Z * Z * Z, uninit size_t; True%I.

  Goal ∀ (l : loc) fn, l ◁ᵥ l @ function_ptr test_fn2 -∗ typed_function fn test_fn.
  Abort.
End test.
