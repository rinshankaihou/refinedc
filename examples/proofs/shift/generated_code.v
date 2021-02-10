From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/shift.c]. *)
Section code.
  Definition file_0 : string := "examples/shift.c".
  Definition loc_2 : location_info := LocationInfo file_0 6 2 6 16.
  Definition loc_3 : location_info := LocationInfo file_0 6 9 6 15.
  Definition loc_4 : location_info := LocationInfo file_0 6 9 6 10.
  Definition loc_5 : location_info := LocationInfo file_0 6 9 6 10.
  Definition loc_6 : location_info := LocationInfo file_0 6 14 6 15.
  Definition loc_9 : location_info := LocationInfo file_0 14 2 14 16.
  Definition loc_10 : location_info := LocationInfo file_0 14 9 14 15.
  Definition loc_11 : location_info := LocationInfo file_0 14 9 14 10.
  Definition loc_12 : location_info := LocationInfo file_0 14 9 14 10.
  Definition loc_13 : location_info := LocationInfo file_0 14 14 14 15.

  (* Definition of function [times_two]. *)
  Definition impl_times_two : function := {|
    f_args := [
      ("x", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 ((LocInfoE loc_4 (use{it_layout u32} (LocInfoE loc_5 ("x")))) <<{IntOp u32, IntOp u32} (LocInfoE loc_6 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_6 (i2v 1 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [div_two]. *)
  Definition impl_div_two : function := {|
    f_args := [
      ("x", it_layout u32)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_9 ;
        Return (LocInfoE loc_10 ((LocInfoE loc_11 (use{it_layout u32} (LocInfoE loc_12 ("x")))) >>{IntOp u32, IntOp u32} (LocInfoE loc_13 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_13 (i2v 1 i32))))))
      ]> $∅
    )%E
  |}.
End code.
