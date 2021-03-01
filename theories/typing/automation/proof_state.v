From refinedc.typing Require Import type.
From refinedc.lithium Require Import tactics.
From refinedc.typing.automation Require Import solvers.

(** * Markers for keeping track of the proof state *)
Definition CURRENT_LOCATION (i : list location_info) (up_to_date : bool) : Set := unit.
Arguments CURRENT_LOCATION : simpl never.
Definition CASE_DISTINCTION_INFO {B} (hint : destruct_hint_info) (info : B) (i : list location_info) : Set := unit.
Arguments CASE_DISTINCTION_INFO : simpl never.

Definition pop_location_info {A} (i : location_info) (a : A) : A := a.
Arguments pop_location_info : simpl never.
Typeclasses Opaque pop_location_info.

Definition BLOCK_PRECOND `{!typeG Σ} (bid : label) (P : iProp Σ) : Set := unit.
Arguments BLOCK_PRECOND : simpl never.

(** * Tactics for manipulating location information *)
Ltac get_loc_info cont :=
  first [ lazymatch reverse goal with
          | H : CURRENT_LOCATION ?icur _ |- _ => cont icur
          end | cont constr:(@nil location_info)
        ].

Ltac update_loc_info i :=
  first [
      lazymatch reverse goal with
      | H : CURRENT_LOCATION ?icur _ |- _ =>
        lazymatch i with
        | Some ?i2 =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION [i2] true) in H
        (* Push *)
        | [ ?i2 ] =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION (i2 :: icur) true) in H
        (* Pop *)
        | [ ?i2; _ ] =>
          lazymatch icur with
          | i2 :: ?iprevh :: ?iprevt =>
            change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION (iprevh :: iprevt) true) in H
          | [i2] =>
            change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION ([i2]) false) in H
          | _ => fail 2 "mismatched pop!"
          end
        | None =>
          change (CURRENT_LOCATION _ _) with (CURRENT_LOCATION icur false) in H
        end
      end
    |
    (* TODO: unify the first two branches *)
    lazymatch i with
    | Some ?i2 => let Hcur := fresh "HCURLOC" in pose (Hcur := ());
      change (unit) with (CURRENT_LOCATION [i2] true) in Hcur
    | [?i2] => let Hcur := fresh "HCURLOC" in pose (Hcur := ());
      change (unit) with (CURRENT_LOCATION [i2] true) in Hcur
    | None => idtac
    end
    ].

Ltac add_case_distinction_info hint info :=
    get_loc_info ltac:(fun icur =>
    let Hcase := fresh "Hcase" in
    pose (Hcase := () : (CASE_DISTINCTION_INFO hint info icur))).

(** * Tactics cleaning the proof state *)
Ltac clear_unused_vars :=
  repeat match goal with
         | H : ?T |- _ =>
           (* don't clear case distinction info or location info  *)
           assert_fails (clearbody H);
           let ty := (type of T) in
           match ty with | Type => clear H | Set => clear H end
         end.

Ltac prepare_sideconditions :=
  liUnfoldLetsInContext;
  liUnfoldAllEvars;
  repeat match goal with | H : BLOCK_PRECOND _ _ |- _ => clear H end;
  (* get rid of Q *)
  try match goal with
      | H : gmap label stmt |- _ => clear H
      end;
  clear_unused_vars.

Ltac solve_goal :=
  try fast_done;
  prepare_sideconditions;
  repeat match goal with | H : CASE_DISTINCTION_INFO _ _ _ |- _ =>  clear H end;
  unprepared_solve_goal.

(** * Tactics for showing failures to the user *)
Ltac clear_for_print_goal :=
  repeat match goal with | H : BLOCK_PRECOND _ _ |- _ => clear H end.

Ltac print_goal :=
  clear_for_print_goal;
  try lazymatch reverse goal with
      | H : CURRENT_LOCATION ?l ?up_to_date |- _ =>
        let rec print_loc_info l :=
            match l with
            | ?i :: ?l =>
              lazymatch eval unfold i in i with
              | LocationInfo ?f ?ls ?cs ?le ?ce =>
                let f := eval unfold f in f in
                idtac "Location:" f "[" ls ":" cs "-" le ":" ce "]";
                print_loc_info l
              end
            | [] => idtac "up to date:" up_to_date
            end in
        print_loc_info l;
        clear H
      end;
   repeat lazymatch reverse goal with
          | H : CASE_DISTINCTION_INFO ?hint ?i ?l |- _ =>
            lazymatch i with
            | (?a, ?b) => idtac "Case distinction" a "->" b
            | ?a => idtac "Case distinction" a
            end;
            lazymatch l with
            | ?i :: ?l =>
              lazymatch eval unfold i in i with
              | LocationInfo ?f ?ls ?cs ?le ?ce =>
                let f := eval unfold f in f in
                idtac "at" f "[" ls ":" cs "-" le ":" ce "]"
              end
            | [] => idtac
            end;
            clear H
          end;
  idtac "Goal:";
  try match reverse goal with
  | H : ?X |- _ => idtac H ":" X; fail
  end;
  idtac "---------------------------------------";
  match goal with
  | |- ?G => idtac G
  end;
  idtac "";
  idtac "".

Ltac print_typesystem_goal fn block :=
  idtac "Type system got stuck in function" fn "in block" block "!";
  print_goal; admit.

Ltac print_sidecondition_goal fn :=
  idtac "Cannot solve sidecondition in function" fn "!";
  print_goal; admit.
