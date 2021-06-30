From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/spinlock.c]. *)
Section code.
  Definition file_0 : string := "examples/spinlock.c".
  Definition loc_2 : location_info := LocationInfo file_0 8 3 8 18.
  Definition loc_3 : location_info := LocationInfo file_0 8 3 8 13.
  Definition loc_4 : location_info := LocationInfo file_0 8 3 8 7.
  Definition loc_5 : location_info := LocationInfo file_0 8 3 8 7.
  Definition loc_6 : location_info := LocationInfo file_0 8 16 8 17.
  Definition loc_9 : location_info := LocationInfo file_0 12 2 12 21.
  Definition loc_10 : location_info := LocationInfo file_0 14 2 16 3.
  Definition loc_11 : location_info := LocationInfo file_0 14 2 16 3.
  Definition loc_12 : location_info := LocationInfo file_0 14 142 16 3.
  Definition loc_13 : location_info := LocationInfo file_0 15 4 15 17.
  Definition loc_14 : location_info := LocationInfo file_0 14 2 16 3.
  Definition loc_15 : location_info := LocationInfo file_0 14 2 16 3.
  Definition loc_16 : location_info := LocationInfo file_0 15 4 15 12.
  Definition loc_17 : location_info := LocationInfo file_0 15 15 15 16.
  Definition loc_18 : location_info := LocationInfo file_0 14 8 14 140.
  Definition loc_19 : location_info := LocationInfo file_0 14 8 14 128.
  Definition loc_20 : location_info := LocationInfo file_0 14 8 14 57.
  Definition loc_21 : location_info := LocationInfo file_0 14 58 14 69.
  Definition loc_22 : location_info := LocationInfo file_0 14 59 14 69.
  Definition loc_23 : location_info := LocationInfo file_0 14 59 14 63.
  Definition loc_24 : location_info := LocationInfo file_0 14 59 14 63.
  Definition loc_25 : location_info := LocationInfo file_0 14 71 14 80.
  Definition loc_26 : location_info := LocationInfo file_0 14 72 14 80.
  Definition loc_27 : location_info := LocationInfo file_0 14 82 14 83.
  Definition loc_28 : location_info := LocationInfo file_0 14 132 14 140.
  Definition loc_29 : location_info := LocationInfo file_0 14 139 14 140.
  Definition loc_30 : location_info := LocationInfo file_0 12 19 12 20.
  Definition loc_35 : location_info := LocationInfo file_0 21 2 21 72.
  Definition loc_36 : location_info := LocationInfo file_0 21 2 21 33.
  Definition loc_37 : location_info := LocationInfo file_0 21 34 21 45.
  Definition loc_38 : location_info := LocationInfo file_0 21 35 21 45.
  Definition loc_39 : location_info := LocationInfo file_0 21 35 21 39.
  Definition loc_40 : location_info := LocationInfo file_0 21 35 21 39.
  Definition loc_41 : location_info := LocationInfo file_0 21 47 21 48.
  Definition loc_44 : location_info := LocationInfo file_0 25 2 31 2.
  Definition loc_45 : location_info := LocationInfo file_0 25 35 28 2.
  Definition loc_46 : location_info := LocationInfo file_0 26 2 26 13.
  Definition loc_47 : location_info := LocationInfo file_0 27 2 27 13.
  Definition loc_48 : location_info := LocationInfo file_0 27 2 27 9.
  Definition loc_49 : location_info := LocationInfo file_0 27 2 27 9.
  Definition loc_50 : location_info := LocationInfo file_0 27 10 27 11.
  Definition loc_51 : location_info := LocationInfo file_0 27 10 27 11.
  Definition loc_52 : location_info := LocationInfo file_0 26 2 26 9.
  Definition loc_53 : location_info := LocationInfo file_0 26 2 26 9.
  Definition loc_54 : location_info := LocationInfo file_0 26 10 26 11.
  Definition loc_55 : location_info := LocationInfo file_0 26 10 26 11.
  Definition loc_56 : location_info := LocationInfo file_0 28 8 31 2.
  Definition loc_57 : location_info := LocationInfo file_0 29 2 29 13.
  Definition loc_58 : location_info := LocationInfo file_0 30 2 30 13.
  Definition loc_59 : location_info := LocationInfo file_0 30 2 30 9.
  Definition loc_60 : location_info := LocationInfo file_0 30 2 30 9.
  Definition loc_61 : location_info := LocationInfo file_0 30 10 30 11.
  Definition loc_62 : location_info := LocationInfo file_0 30 10 30 11.
  Definition loc_63 : location_info := LocationInfo file_0 29 2 29 9.
  Definition loc_64 : location_info := LocationInfo file_0 29 2 29 9.
  Definition loc_65 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_66 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_67 : location_info := LocationInfo file_0 25 6 25 33.
  Definition loc_68 : location_info := LocationInfo file_0 25 6 25 18.
  Definition loc_69 : location_info := LocationInfo file_0 25 17 25 18.
  Definition loc_70 : location_info := LocationInfo file_0 25 17 25 18.
  Definition loc_71 : location_info := LocationInfo file_0 25 21 25 33.
  Definition loc_72 : location_info := LocationInfo file_0 25 32 25 33.
  Definition loc_73 : location_info := LocationInfo file_0 25 32 25 33.

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
      ("lock", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_3 ((LocInfoE loc_4 (!{void*} (LocInfoE loc_5 ("lock")))) at{struct_spinlock} "lock") <-{ it_layout bool_it, ScOrd }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_6 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [sl_lock]. *)
  Definition impl_sl_lock : function := {|
    f_args := [
      ("lock", void*)
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
        if: LocInfoE loc_18 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_18 ((LocInfoE loc_19 (UnOp (CastOp $ IntOp i32) (IntOp bool_it) (LocInfoE loc_19 (CAS
            (IntOp bool_it)
            (LocInfoE loc_21 (&(LocInfoE loc_22 ((LocInfoE loc_23 (!{void*} (LocInfoE loc_24 ("lock")))) at{struct_spinlock} "lock"))))
            (LocInfoE loc_25 (&(LocInfoE loc_26 ("expected"))))
            (LocInfoE loc_27 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_27 (i2v 1 i32)))))))) ={IntOp i32, IntOp i32} (LocInfoE loc_28 (UnOp (CastOp $ IntOp i32) (IntOp bool_it) (LocInfoE loc_28 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_29 (i2v 0 i32)))))))))
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
      ("lock", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_35 ;
        LocInfoE loc_38 ((LocInfoE loc_39 (!{void*} (LocInfoE loc_40 ("lock")))) at{struct_spinlock} "lock") <-{ it_layout bool_it, ScOrd }
          LocInfoE loc_41 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_41 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [sl_lock_both]. *)
  Definition impl_sl_lock_both (global_sl_lock : loc): function := {|
    f_args := [
      ("a", void*);
      ("b", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_67 ;
        if: LocInfoE loc_67 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_67 ((LocInfoE loc_68 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_69 (use{void*} (LocInfoE loc_70 ("a")))))) <{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_71 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_72 (use{void*} (LocInfoE loc_73 ("b")))))))))
        then
        locinfo: loc_46 ;
          Goto "#1"
        else
        locinfo: loc_57 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_46 ;
        expr: (LocInfoE loc_46 (Call (LocInfoE loc_53 (global_sl_lock)) [@{expr} LocInfoE loc_54 (use{void*} (LocInfoE loc_55 ("a"))) ])) ;
        locinfo: loc_47 ;
        expr: (LocInfoE loc_47 (Call (LocInfoE loc_49 (global_sl_lock)) [@{expr} LocInfoE loc_50 (use{void*} (LocInfoE loc_51 ("b"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_57 ;
        expr: (LocInfoE loc_57 (Call (LocInfoE loc_64 (global_sl_lock)) [@{expr} LocInfoE loc_65 (use{void*} (LocInfoE loc_66 ("b"))) ])) ;
        locinfo: loc_58 ;
        expr: (LocInfoE loc_58 (Call (LocInfoE loc_60 (global_sl_lock)) [@{expr} LocInfoE loc_61 (use{void*} (LocInfoE loc_62 ("a"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
