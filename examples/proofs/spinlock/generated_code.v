From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [examples/spinlock.c]. *)
Section code.
  Definition file_0 : string := "examples/spinlock.c".
  Definition loc_2 : location_info := LocationInfo file_0 6 4 6 19.
  Definition loc_3 : location_info := LocationInfo file_0 6 4 6 14.
  Definition loc_4 : location_info := LocationInfo file_0 6 4 6 8.
  Definition loc_5 : location_info := LocationInfo file_0 6 4 6 8.
  Definition loc_6 : location_info := LocationInfo file_0 6 17 6 18.
  Definition loc_9 : location_info := LocationInfo file_0 11 4 11 23.
  Definition loc_10 : location_info := LocationInfo file_0 12 4 14 5.
  Definition loc_11 : location_info := LocationInfo file_0 12 4 14 5.
  Definition loc_12 : location_info := LocationInfo file_0 12 144 14 5.
  Definition loc_13 : location_info := LocationInfo file_0 13 8 13 21.
  Definition loc_14 : location_info := LocationInfo file_0 12 4 14 5.
  Definition loc_15 : location_info := LocationInfo file_0 12 4 14 5.
  Definition loc_16 : location_info := LocationInfo file_0 13 8 13 16.
  Definition loc_17 : location_info := LocationInfo file_0 13 19 13 20.
  Definition loc_18 : location_info := LocationInfo file_0 12 10 12 142.
  Definition loc_19 : location_info := LocationInfo file_0 12 10 12 130.
  Definition loc_20 : location_info := LocationInfo file_0 12 10 12 59.
  Definition loc_21 : location_info := LocationInfo file_0 12 60 12 71.
  Definition loc_22 : location_info := LocationInfo file_0 12 61 12 71.
  Definition loc_23 : location_info := LocationInfo file_0 12 61 12 65.
  Definition loc_24 : location_info := LocationInfo file_0 12 61 12 65.
  Definition loc_25 : location_info := LocationInfo file_0 12 73 12 82.
  Definition loc_26 : location_info := LocationInfo file_0 12 74 12 82.
  Definition loc_27 : location_info := LocationInfo file_0 12 84 12 85.
  Definition loc_28 : location_info := LocationInfo file_0 12 134 12 142.
  Definition loc_29 : location_info := LocationInfo file_0 12 141 12 142.
  Definition loc_30 : location_info := LocationInfo file_0 11 21 11 22.
  Definition loc_35 : location_info := LocationInfo file_0 19 4 19 74.
  Definition loc_36 : location_info := LocationInfo file_0 19 4 19 35.
  Definition loc_37 : location_info := LocationInfo file_0 19 36 19 47.
  Definition loc_38 : location_info := LocationInfo file_0 19 37 19 47.
  Definition loc_39 : location_info := LocationInfo file_0 19 37 19 41.
  Definition loc_40 : location_info := LocationInfo file_0 19 37 19 41.
  Definition loc_41 : location_info := LocationInfo file_0 19 49 19 50.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [sl_init]. *)
  Definition impl_sl_init : function := {|
    f_args := [
      ("lock", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_3 ((LocInfoE loc_4 (!{LPtr} (LocInfoE loc_5 ("lock")))) at{struct_spinlock} "lock") <-{ it_layout bool_it, ScOrd }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_6 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [sl_lock]. *)
  Definition impl_sl_lock : function := {|
    f_args := [
      ("lock", LPtr)
    ];
    f_local_vars := [
      ("expected", it_layout bool_it)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "expected" <-{ it_layout bool_it }
          LocInfoE loc_30 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_30 (i2v 0 i32))) ;
        locinfo: loc_10 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_18 ;
        if: LocInfoE loc_18 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_18 ((LocInfoE loc_19 (CAS
            (IntOp bool_it)
            (LocInfoE loc_21 (&(LocInfoE loc_22 ((LocInfoE loc_23 (!{LPtr} (LocInfoE loc_24 ("lock")))) at{struct_spinlock} "lock"))))
            (LocInfoE loc_25 (&(LocInfoE loc_26 ("expected"))))
            (LocInfoE loc_27 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_27 (i2v 1 i32)))))) ={IntOp bool_it, IntOp bool_it} (LocInfoE loc_28 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_29 (i2v 0 i32)))))))
        then
        locinfo: loc_13 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_13 ;
        LocInfoE loc_16 ("expected") <-{ it_layout bool_it }
          LocInfoE loc_17 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_17 (i2v 0 i32))) ;
        locinfo: loc_14 ;
        Goto "continue4"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "continue4" :=
        locinfo: loc_10 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [sl_unlock]. *)
  Definition impl_sl_unlock : function := {|
    f_args := [
      ("lock", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_35 ;
        LocInfoE loc_38 ((LocInfoE loc_39 (!{LPtr} (LocInfoE loc_40 ("lock")))) at{struct_spinlock} "lock") <-{ it_layout bool_it, ScOrd }
          LocInfoE loc_41 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_41 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
