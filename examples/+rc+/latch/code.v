From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/latch.c]. *)
Section code.
  Definition file_0 : string := "examples/latch.c".
  Definition loc_2 : location_info := LocationInfo file_0 5 2 5 94.
  Definition loc_3 : location_info := LocationInfo file_0 5 2 5 94.
  Definition loc_4 : location_info := LocationInfo file_0 5 92 5 94.
  Definition loc_5 : location_info := LocationInfo file_0 5 2 5 94.
  Definition loc_6 : location_info := LocationInfo file_0 5 2 5 94.
  Definition loc_7 : location_info := LocationInfo file_0 5 8 5 90.
  Definition loc_8 : location_info := LocationInfo file_0 5 8 5 78.
  Definition loc_9 : location_info := LocationInfo file_0 5 8 5 38.
  Definition loc_10 : location_info := LocationInfo file_0 5 39 5 55.
  Definition loc_11 : location_info := LocationInfo file_0 5 40 5 55.
  Definition loc_12 : location_info := LocationInfo file_0 5 40 5 45.
  Definition loc_13 : location_info := LocationInfo file_0 5 40 5 45.
  Definition loc_14 : location_info := LocationInfo file_0 5 82 5 90.
  Definition loc_15 : location_info := LocationInfo file_0 5 89 5 90.
  Definition loc_18 : location_info := LocationInfo file_0 9 2 9 77.
  Definition loc_19 : location_info := LocationInfo file_0 9 2 9 33.
  Definition loc_20 : location_info := LocationInfo file_0 9 34 9 50.
  Definition loc_21 : location_info := LocationInfo file_0 9 35 9 50.
  Definition loc_22 : location_info := LocationInfo file_0 9 35 9 40.
  Definition loc_23 : location_info := LocationInfo file_0 9 35 9 40.
  Definition loc_24 : location_info := LocationInfo file_0 9 52 9 53.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [latch]. *)
  Program Definition struct_latch := {|
    sl_members := [
      (Some "released", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [latch_wait]. *)
  Definition impl_latch_wait : function := {|
    f_args := [
      ("latch", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_7 ;
        if: LocInfoE loc_7 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_7 ((LocInfoE loc_8 (use{it_layout bool_it, ScOrd} (LocInfoE loc_11 ((LocInfoE loc_12 (!{LPtr} (LocInfoE loc_13 ("latch")))) at{struct_latch} "released")))) ={IntOp bool_it, IntOp bool_it} (LocInfoE loc_14 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_15 (i2v 0 i32)))))))
        then
        locinfo: loc_5 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_5 ;
        Goto "continue2"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue2" :=
        locinfo: loc_2 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [latch_release]. *)
  Definition impl_latch_release : function := {|
    f_args := [
      ("latch", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_18 ;
        LocInfoE loc_21 ((LocInfoE loc_22 (!{LPtr} (LocInfoE loc_23 ("latch")))) at{struct_latch} "released") <-{ it_layout bool_it, ScOrd }
          LocInfoE loc_24 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_24 (i2v 1 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
