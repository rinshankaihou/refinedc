From iris.proofmode Require Import coq_tactics reduction.
From refinedc.typing Require Export type.
From refinedc.lithium Require Export tactics.
From refinedc.typing.automation Require Export normalize solvers simplification proof_state loc_eq.
From refinedc.typing Require Import programs function singleton own struct bytes int.
Set Default Proof Using "Type".

(** * Registering extensions *)
(** More automation for modular arithmetics. *)
Ltac Zify.zify_post_hook ::= Z.to_euclidean_division_equations.

(** We use autorewrite for the moment. *)
Ltac normalize_tac ::= normalize_autorewrite.
(* Goal ∀ l i (x : Z), *)
(*     0 < length (<[i:=x]> $ <[i:=x]> (<[length (<[i:=x]>l) :=x]> l ++ <[length (<[i:=x]>l) :=x]> l)). *)
(*   move => ???. normalize_goal. *)
(* Abort. *)

Ltac li_pm_reduce_tac H ::= eval cbv [t2mt mt_type mt_movable] in H.

Ltac custom_exist_tac A protect ::=
    lazymatch A with
    | mtype =>
      lazymatch protect with
      | true => fail 1000 "cannot protect mtype"
      | false =>
      (* it is important that we don't trigger typeclass search here
      as we want to keep Movable as an evar, thus we use notypeclasses
      refine. *)
        notypeclasses refine (ex_intro _ (t2mt _) _)
      end
    | Movable _ => eexists _
    end.

Hint Transparent ly_size : solve_protected_eq_db.
Ltac solve_protected_eq_unfold_tac ::=
  lazymatch goal with
  (* unfold constants for function types *)
  | |- @eq (_ → fn_params) ?a (λ x, _) =>
    lazymatch a with
    | (λ x, _) => idtac
    | _ =>
      let h := get_head a in
      unfold h;
      (* necessary to reduce after unfolding because of the strict
      opaqueness settings for unification *)
      liSimpl
    end
  (* don't fail if nothing matches *)
  | |- _ => idtac
  end.

Ltac can_solve_tac ::= solve_goal.

Ltac record_destruct_hint hint info ::= add_case_distinction_info hint info.

Ltac convert_to_i2p_tac P ::=
  lazymatch P with
  | typed_value ?v ?T => uconstr:(((_ : TypedValue _) _).(i2p_proof))
  | typed_bin_op ?v1 ?ty1 ?v2 ?ty2 ?o ?ot1 ?ot2 ?T => uconstr:(((_ : TypedBinOp _ _ _ _ _ _ _) _).(i2p_proof))
  | typed_un_op ?v ?ty ?o ?ot ?T => uconstr:(((_ : TypedUnOp _ _ _ _) _).(i2p_proof))
  | typed_call ?v ?P ?vl ?tys ?T => uconstr:(((_ : TypedCall _ _ _ _) _).(i2p_proof))
  | typed_copy_alloc_id ?v1 ?ty1 ?v2 ?ty2 ?ot ?T => uconstr:(((_ : TypedCopyAllocId _ _ _ _ _) _).(i2p_proof))
  | typed_place ?P ?l1 ?β1 ?ty1 ?T => uconstr:(((_ : TypedPlace _ _ _ _) _).(i2p_proof))
  | typed_if ?ot ?v ?ty ?T1 ?T2 => uconstr:(((_ : TypedIf _ _ _) _ _).(i2p_proof))
  | typed_switch ?v ?ty ?it ?m ?ss ?def ?fn ?ls ?fr ?Q => uconstr:(((_ : TypedSwitch _ _ _) _ _ _ _ _ _ _).(i2p_proof))
  | typed_assert ?ot ?v ?ty ?s ?fn ?ls ?fr ?Q => uconstr:(((_ : TypedAssert _ _ _) _ _ _ _ _).(i2p_proof))
  | typed_read_end ?a ?l ?β ?ty ?ly ?T => uconstr:(((_ : TypedReadEnd _ _ _ _ _) _).(i2p_proof))
  | typed_write_end ?a ?ot ?v1 ?ty1 ?l2 ?β2 ?ty2 ?T => uconstr:(((_ : TypedWriteEnd _ _ _ _ _ _ _) _).(i2p_proof))
  | typed_addr_of_end ?l ?β ?ty ?T => uconstr:(((_ : TypedAddrOfEnd _ _ _) _).(i2p_proof))
  | typed_cas ?ot ?v1 ?P1 ?v2 ?P2 ?v3 ?P3 ?T => uconstr:(((_ : TypedCas _ _ _ _ _ _ _) _).(i2p_proof))
  | typed_annot_expr ?n ?a ?v ?P ?T => uconstr:(((_ : TypedAnnotExpr _ _ _ _) _) .(i2p_proof))
  | typed_annot_stmt ?a ?l ?P ?T => uconstr:(((_ : TypedAnnotStmt _ _ _) _).(i2p_proof))
  | typed_macro_expr ?m ?es ?T => uconstr:(((_ : TypedMacroExpr _ _) _).(i2p_proof))
  end.

(** * Main automation tactics *)
Section automation.
  Context `{!typeG Σ}.

  Lemma tac_simpl_subst xs s fn ls Q R:
    typed_stmt (W.to_stmt (W.subst_stmt xs s)) fn ls R Q -∗
    typed_stmt (subst_stmt xs (W.to_stmt s)) fn ls R Q.
  Proof. by rewrite W.to_stmt_subst. Qed.

  Lemma tac_typed_single_block_rec P b Q fn ls R s:
    Q !! b = Some s →
    (P ∗ accu (λ A, typed_block (P ∗ A) b fn ls R Q -∗ P -∗ A -∗ typed_stmt s fn ls R Q)) -∗
    typed_stmt (Goto b) fn ls R Q.
  Proof.
    iIntros (HQ) "[HP Hs]". iIntros (Hls). unfold accu, typed_block.
    iDestruct "Hs" as (A) "[HA #Hs]". iLöb as "Hl".
    iApply wps_goto =>//. iModIntro. iApply ("Hs" with "[] HP HA") => //.
    iIntros "!# [HP HA]". by iApply ("Hl" with "HP HA").
  Qed.
End automation.

Ltac liRIntroduceLetInGoal :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ ?P =>
    let H := fresh "GOAL" in
    lazymatch P with
    | @bi_wand ?PROP ?Q ?T =>
      pose H := (LET_ID T); change_no_check (@envs_entails PROP Δ (@bi_wand PROP Q H))
    | @typed_val_expr ?Σ ?tG ?e ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_val_expr Σ tG e H))
    | @typed_write ?Σ ?tG ?b ?e ?ot ?v ?ty ?Mov ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_write Σ tG b e ot v ty Mov H))
    | @typed_place ?Σ ?tG ?P ?l1 ?β1 ?ty1 ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_place Σ tG P l1 β1 ty1 H))
    | @typed_bin_op ?Σ ?tG ?v1 ?P1 ?v2 ?P2 ?op ?ot1 ?ot2 ?T =>
      pose (H := LET_ID T); change_no_check (@envs_entails PROP Δ (@typed_bin_op Σ tG v1 P1 v2 P2 op ot1 ot2 H))
    end
  end.

Ltac liRInstantiateEvars_hook := idtac.
Ltac liRInstantiateEvars :=
  liRInstantiateEvars_hook;
  lazymatch goal with
  | |- (_ < protected ?H)%nat ∧ _ =>
    (* We would like to use [liInst H (S (protected (EVAR_ID _)))],
      but this causes a Error: No such section variable or assumption
      at Qed. time. Maybe this is related to https://github.com/coq/coq/issues/9937 *)
    instantiate_protected (protected H) ltac:(fun H => instantiate (1:=((S (protected (EVAR_ID _))))) in (Value of H))
  (* This is very hard to figure out for unification because of the
  dependent types in with refinement. Unificaiton likes to unfold the
  definition of ty without this. This is the reason why do_instantiate
  evars must come before do_side_cond *)
  | |- protected ?H = ( _ @ ?ty)%I ∧ _ =>
    instantiate_protected (protected H) ltac:(fun H => instantiate (1:=((protected (EVAR_ID _)) @ ty)%I) in (Value of H))
  | |- protected ?H = ty_of_rty (frac_ptr ?β _)%I ∧ _ =>
    instantiate_protected (protected H) ltac:(fun H => instantiate (1:=((frac_ptr β (protected (EVAR_ID _)))%I)) in (Value of H))
  | |- envs_entails _ (subsume (?x ◁ₗ{?β} ?ty) (_ ◁ₗ{_} (protected ?H)) _) => liInst H ty
  | |- envs_entails _ (subsume (?x ◁ₗ{?β} ?ty) (_ ◁ₗ{protected ?H} _) _) => liInst H β
  end.

Ltac liRStmt :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?s ?fn ?ls ?fr ?Q) =>
    lazymatch s with
    | LocInfo ?info ?s2 =>
      update_loc_info (Some info);
      change_no_check (envs_entails Δ (typed_stmt s2 fn ls fr Q))
    | _ => update_loc_info (None : option location_info)
    end
  end;
  lazymatch goal with
  | |- envs_entails ?Δ (typed_stmt ?s ?fn ?ls ?fr ?Q) =>
    lazymatch s with
    | subst_stmt ?xs ?s =>
      let s' := W.of_stmt s in
      change (subst_stmt xs s) with (subst_stmt xs (W.to_stmt s'));
      refine (tac_fast_apply (tac_simpl_subst _ _ _ _ _ _) _); simpl; unfold W.to_stmt, W.to_expr
    | _ =>
      let s' := W.of_stmt s in
      lazymatch s' with
      | W.Assign _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_assign _ _ _ _ _ _ _ _ _) _)
      | W.Return _ => notypeclasses refine (tac_fast_apply (type_return _ _ _ _ _) _)
      | W.IfS _ _ _ _ => notypeclasses refine (tac_fast_apply (type_if _ _ _ _ _ _ _ _) _)
      | W.Switch _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_switch _ _ _ _ _ _ _ _ _) _)
      | W.Assert _ _ _ => notypeclasses refine (tac_fast_apply (type_assert _ _ _ _ _ _ _) _)
      | W.Goto ?bid => first [
         notypeclasses refine (tac_fast_apply (type_goto_precond _ _ _ _ _ _) _); progress liFindHyp FICSyntactic
       | lazymatch goal with
         | H : BLOCK_PRECOND bid ?P |- _ =>
           notypeclasses refine (tac_fast_apply (tac_typed_single_block_rec P _ _ _ _ _ _ _) _);[unfold_code_marker_and_compute_map_lookup|]
         end
       | notypeclasses refine (tac_fast_apply (type_goto _ _ _ _ _ _ _) _); [unfold_code_marker_and_compute_map_lookup|]
                     ]
      | W.ExprS _ _ => notypeclasses refine (tac_fast_apply (type_exprs _ _ _ _ _ _) _)
      | W.SkipS _ => notypeclasses refine (tac_fast_apply (type_skips' _ _ _ _ _) _)
      | W.AnnotStmt _ ?a _ => notypeclasses refine (tac_fast_apply (type_annot_stmt _ _ _ _ _ _ _) _)
      | _ => fail "do_stmt: unknown stmt" s
      end
    end
  end.

Ltac liRIntroduceTypedStmt :=
  lazymatch goal with
  | |- @envs_entails ?PROP ?Δ (introduce_typed_stmt ?fn ?ls ?R) =>
    iEval (rewrite /introduce_typed_stmt !fmap_insert fmap_empty; simpl_subst);
      lazymatch goal with
      | |- @envs_entails ?PROP ?Δ (@typed_stmt ?Σ ?tG ?s ?fn ?ls ?R ?Q) =>
        let HQ := fresh "Q" in
        let HR := fresh "R" in
        pose (HQ := (CODE_MARKER Q));
        pose (HR := (RETURN_MARKER R));
        change_no_check (@envs_entails PROP Δ (@typed_stmt Σ tG s fn ls HR HQ));
        iEval (simpl) (* To simplify f_init *)
      end
  end.

Ltac liRPopLocationInfo :=
  lazymatch goal with
  (* TODO: don't hardcode this for two arguments *)
  | |- envs_entails ?Δ (pop_location_info ?info ?T ?a1 ?a2) =>
    update_loc_info [info; info];
    change_no_check (envs_entails Δ (T a1 a2))
  end.

Ltac liRExpr :=
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?e ?T) =>
    lazymatch e with
    | LocInfo ?info ?e2 =>
      update_loc_info [info];
      change_no_check (envs_entails Δ (typed_val_expr e2 (pop_location_info info T)))
    | _ => idtac
    end
  end;
  lazymatch goal with
  | |- envs_entails ?Δ (typed_val_expr ?e ?T) =>
    let e' := W.of_expr e in
    lazymatch e' with
    | W.Val _ => notypeclasses refine (tac_fast_apply (type_val _ _) _)
    | W.Loc _ => notypeclasses refine (tac_fast_apply (type_val _ _) _)
    | W.Use _ _ _ => notypeclasses refine (tac_fast_apply (type_use _ _ _ _) _)
    | W.AddrOf _ => notypeclasses refine (tac_fast_apply (type_addr_of _ _) _)
    | W.BinOp _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_bin_op _ _ _ _ _ _) _)
    | W.CopyAllocId _ _ _ => notypeclasses refine (tac_fast_apply (type_copy_alloc_id _ _ _ _) _)
    | W.UnOp _ _ _ => notypeclasses refine (tac_fast_apply (type_un_op _ _ _ _) _)
    | W.CAS _ _ _ _ => notypeclasses refine (tac_fast_apply (type_cas _ _ _ _ _) _)
    | W.Call _ _ => notypeclasses refine (tac_fast_apply (type_call _ _ _) _)
    | W.OffsetOf _ _ => notypeclasses refine (tac_fast_apply (type_offset_of _ _ _) _)
    | W.AnnotExpr _ ?a _ => notypeclasses refine (tac_fast_apply (type_annot_expr _ _ _ _) _)
    | W.StructInit _ _ => notypeclasses refine (tac_fast_apply (type_struct_init _ _ _) _)
    | W.IfE _ _ _ _ => notypeclasses refine (tac_fast_apply (type_ife _ _ _ _ _) _)
    | W.LogicalAnd _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_and _ _ _ _ _) _)
    | W.LogicalOr _ _ _ _ _ => notypeclasses refine (tac_fast_apply (type_logical_or _ _ _ _ _) _)
    | W.SkipE _ => notypeclasses refine (tac_fast_apply (type_skipe' _ _) _)
    | W.MacroE _ _ _ => notypeclasses refine (tac_fast_apply (type_macro_expr _ _ _) _)
    | _ => fail "do_expr: unknown expr" e
    end
  end.

Ltac liRJudgement :=
  lazymatch goal with
    | |- envs_entails _ (typed_write _ _ _ _ _ _) => notypeclasses refine (tac_fast_apply (type_write _ _ _ _ _ _ _ _) _); [ solve [refine _ ] |]
    | |- envs_entails _ (typed_read _ _ _ _) => notypeclasses refine (tac_fast_apply (type_read _ _ _ _ _ _) _); [ solve [refine _ ] |]
    | |- envs_entails _ (typed_addr_of _ _) => notypeclasses refine (tac_fast_apply (type_addr_of_place _ _ _ _) _); [solve [refine _] |]
  end.

(* This does everything *)
Ltac liRStep :=
 liEnforceInvariantAndUnfoldInstantiatedEvars;
 try liRIntroduceLetInGoal;
 first [
   liRInstantiateEvars (* must be before do_side_cond and do_extensible_judgement *)
 | liRPopLocationInfo
 | liRStmt
 | liRIntroduceTypedStmt
 | liRExpr
 | liRJudgement
 | liStep
]; liSimpl.

Tactic Notation "liRStepUntil" open_constr(id) :=
  repeat lazymatch goal with
         | |- @environments.envs_entails _ _ ?P =>
           lazymatch P with
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ _ => fail
           | id _ _ _ _ _ _ => fail
           | id _ _ _ _ _ => fail
           | id _ _ _ _ => fail
           | id _ _ => fail
           | id _ => fail
           | id => fail
           | _  => liRStep
           end
         | _ => liRStep
  end; liShow.


(** * Tactics for starting a function *)
(* Recursively destruct a product in hypothesis H, using the given name as template. *)
Ltac destruct_product_hypothesis name H :=
  match goal with
  | H : _ * _ |- _ => let tmp1 := fresh "tmp" in
                      let tmp2 := fresh "tmp" in
                      destruct H as [tmp1 tmp2];
                      destruct_product_hypothesis name tmp1;
                      destruct_product_hypothesis name tmp2
  |           |- _ => let id := fresh name in
                      rename H into id
  end.

Ltac prepare_initial_coq_context :=
  (* The automation assumes that all products in the context are destructed, see liForall *)
  repeat lazymatch goal with
  | H : _ * _ |- _ => destruct_product_hypothesis H H
  | H : unit |- _ => destruct H
  end.

(* IMPORTANT: We need to make sure to never call simpl while the code
(Q) is part of the goal, because simpl seems to take exponential time
in the number of blocks! *)
(* TODO: don't use i... tactics here *)
Tactic Notation "start_function" constr(fnname) "(" simple_intropattern(x) ")" :=
  intros;
  repeat iIntros "#?";
  rewrite /typed_function;
  iIntros ( x );
  iSplit; [iPureIntro; simpl; by [repeat constructor] || fail "in" fnname "argument types don't match layout of arguments" |];
  let lsa := fresh "lsa" in let lsv := fresh "lsv" in
  iIntros "!#" (lsa lsv); inv_vec lsv; inv_vec lsa; prepare_initial_coq_context.

Ltac liRSplitBlocksIntro :=
  repeat (
      liEnforceInvariantAndUnfoldInstantiatedEvars;
      first [
          liSep
        | liWand
        | liImpl
        | liForall
        | liExist true
        | liUnfoldLetGoal]; liSimpl);
  liShow.

(* TODO: don't use i... tactics here *)
Ltac split_blocks Pfull Ps :=
  (* cbn in * is important here to simplify the types of local
  variables, otherwise unification gets confused later *)
  cbn -[union] in *;
  let rec pose_Ps Ps :=
      lazymatch Ps with
      | <[?bid:=?P]>?m =>
        let Hblock := fresh "Hblock" in
        have Hblock: (BLOCK_PRECOND bid P) by exact: tt;
        pose_Ps m
      | _ => idtac
      end
  in
  pose_Ps Ps;
  let Hfull := fresh "Hfull" in
  (* We must do this pose first since do_split_block_intro might call
  subst and we want to subst in Ps as well. *)
  pose (Hfull := Pfull);
  liRSplitBlocksIntro;
  liRIntroduceTypedStmt;
  iApply (typed_block_rec Hfull); unfold Hfull; clear Hfull; last first; [|
  repeat (iApply big_sepM_insert; [reflexivity|]; iSplitL); last by [iApply big_sepM_empty];
  iExists _; (iSplitR; [iPureIntro; unfold_code_marker_and_compute_map_lookup|]); iModIntro ];
  repeat (iApply tac_split_big_sepM; [reflexivity|]; iIntros "?"); iIntros "_".
