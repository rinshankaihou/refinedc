From refinedc.typing Require Import type.
From refinedc.lithium Require Import tactics.

(** * [refined_solver]
    Version of naive_solver which fails faster. *)
Tactic Notation "refined_solver" tactic(tac) :=
  unfold iff, not in *;
  repeat match goal with
  | H : context [∀ _, _ ∧ _ ] |- _ =>
    repeat setoid_rewrite forall_and_distr in H; revert H
  | H : context [Is_true _ ] |- _ =>
    repeat setoid_rewrite Is_true_eq in H
  | |- Is_true _ => repeat setoid_rewrite Is_true_eq
  end;
  let rec go :=
  repeat match goal with
  (**i solve the goal *)
  | |- _ => fast_done
  (**i intros *)
  | |- ∀ _, _ => intro
  (**i simplification of assumptions *)
  | H : False |- _ => destruct H
  | H : _ ∧ _ |- _ =>
     (* Work around bug https://coq.inria.fr/bugs/show_bug.cgi?id=2901 *)
     let H1 := fresh in let H2 := fresh in
     destruct H as [H1 H2]; try clear H
  | H : ∃ _, _  |- _ =>
     let x := fresh in let Hx := fresh in
     destruct H as [x Hx]; try clear H
  | H : ?P → ?Q, H2 : ?P |- _ => specialize (H H2)
  (**i simplify and solve equalities *)
  (* | |- _ => progress simplify_eq/= *)
  | |- _ => progress subst; csimpl in *
  (**i operations that generate more subgoals *)
  | |- _ ∧ _ => split
  (* | |- Is_true (bool_decide _) => apply (bool_decide_pack _) *)
  (* | |- Is_true (_ && _) => apply andb_True; split *)
  | H : _ ∨ _ |- _ =>
     let H1 := fresh in destruct H as [H1|H1]; try clear H
  (* | H : Is_true (_ || _) |- _ => *)
     (* apply orb_True in H; let H1 := fresh in destruct H as [H1|H1]; try clear H *)
  (**i solve the goal using the user supplied tactic *)
  | |- _ => solve [tac]
  end;
  (**i use recursion to enable backtracking on the following clauses. *)
  match goal with
  (**i instantiation of the conclusion *)
  | |- ∃ x, _ => no_new_unsolved_evars ltac:(eexists; go)
  | |- _ ∨ _ => first [left; go | right; go]
  (* | |- Is_true (_ || _) => apply orb_True; first [left; go | right; go] *)
  | _ =>
    (**i instantiations of assumptions. *)
    match goal with
    | H : ?P → ?Q |- _ =>
      let H' := fresh "H" in
      assert P as H'; [clear H; go|];
      specialize (H H'); clear H'; go
    end
  end in go.
Tactic Notation "refined_solver" := refined_solver eauto.

(** * [normalize_and_simpl_goal] *)
Lemma intro_and_True P :
  (P ∧ True) → P.
Proof. naive_solver. Qed.

Ltac normalize_and_simpl_goal_step :=
  first [
      progress normalize_goal; simpl |
              lazymatch goal with
              | |- ∃ _, _ => fail 1 "normalize_and_simpl_goal stop in exist"
              end
              |
              lazymatch goal with
              | |- _ ∧ _ => idtac
              | _ => refine (intro_and_True _ _)
              end;
              refine (apply_simpl_and _ _ _ _ _);
              lazymatch goal with
              | |- true = true → _ => move => _; split_and?
              end
              | lazymatch goal with
    (* relying on the fact that unification variables cannot contain
       dependent variables to distinguish between dependent and non dependent forall *)
    | |- ?P -> ?Q =>
      lazymatch type of P with
      | Prop => first [
        progress normalize_goal_impl |
        notypeclasses refine (apply_simpl_impl _ _ _ _ _); [ solve [refine _] |]; simpl;
        match goal with
        | |- true = true -> _ => move => _
        | |- false = false -> ?P → _ => move => _;
          match P with
          | ∃ _, _ => case
          | _ = _ => let Hi := fresh "Hi" in move => Hi; injection Hi; clear Hi
          | _ => check_hyp_not_exists P; intros ?; subst
          | _ => move => _
          end
        end]
      (* just some unused variable, forget it *)
      | _ => move => _
      end
    | |- forall _ : ?P, _ =>
      lazymatch P with
      | (prod _ _) => case
      | unit => case
      | _ => intro
      end
    end ].

Ltac normalize_and_simpl_goal := repeat normalize_and_simpl_goal_step.

(** * [compute_map_lookup] *)
Ltac compute_map_lookup :=
  lazymatch goal with
  | |- ?Q !! _ = Some _ => try (is_var Q; unfold Q)
  | _ => fail "unknown goal for compute_map_lookup"
  end;
  solve [repeat lazymatch goal with
  | |- <[?x:=?s]> ?Q !! ?y = Some ?res =>
    lazymatch x with
    | y => change_no_check (Some s = Some res); reflexivity
    | _ => change_no_check (Q !! y = Some res)
    end
  end ].

(** * Enriching the context for lia  *)
Definition enrich_marker {A} (f : A) : A := f.
Ltac enrich_context_base :=
    repeat match goal with
         | |- context C [ ?a `quot` ?b ] =>
           let G := context C[enrich_marker Z.quot a b] in
           change_no_check G;
           try have ?:=Z.quot_lt a b ltac:(lia) ltac:(lia);
           try have ?:=Z.quot_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ ?a `rem` ?b ] =>
           let G := context C[enrich_marker Z.rem a b] in
           change_no_check G;
           try have ?:=Z.rem_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ ?a `mod` ?b ] =>
           let G := context C[enrich_marker Z.modulo a b] in
           change_no_check G;
           try have ?:=Z.mod_bound_pos a b ltac:(lia) ltac:(lia)
         | |- context C [ length (filter ?P ?l) ] =>
           let G := context C[enrich_marker length (filter P l)] in
           change_no_check G;
           pose proof (filter_length P l)
           end.

Ltac enrich_context_tac :=
  enrich_context_base.

Ltac enrich_context :=
  enrich_context_tac;
  unfold enrich_marker.

(* Goal ∀ n m, 0 < n → 1 < m → n `quot` m = n `rem` m. *)
(*   move => n m ??. enrich_context. *)
(* Abort. *)

Lemma unfold_int_elem_of_it (z : Z) (it : int_type) :
  z ∈ it = (min_int it ≤ z ∧ z ≤ max_int it).
Proof. done. Qed.

(** * [solve_goal] without cleaning of the context  *)
Ltac unprepared_solve_goal :=
  try rewrite -> unfold_int_elem_of_it in *;
  unfold ly_size, ly_align_log, max_int, min_int, int_half_modulus, int_modulus in *; simpl in *;
  normalize_and_simpl_goal;
  rewrite /ly_size/ly_align_log //=; enrich_context;
  repeat case_bool_decide => //; repeat case_decide => //; repeat case_match => //;
  refined_solver lia.

(** * Tactics for solving sideconditions in ..._spec.v files  *)
Ltac solve_rmovable :=
  simple notypeclasses refine ({| rmovable n := _; rmove_layout x1 x2 := _ |}); [
    unfold with_refinement => /=; by apply _|
    simpl; solve_typing
  ].

Ltac solve_ty_layout_eq :=
  simpl;
  repeat lazymatch goal with
    | |- ∀ _ : (_ * _), _ => case
    | |- ∀ _ : _, _ => move => ?
    end;
  by rewrite /ty_layout.
