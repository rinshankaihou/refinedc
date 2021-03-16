From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_2.c]. *)
Section code.
  Definition file_0 : string := "examples/paper_example_2_2.c".
  Definition loc_2 : location_info := LocationInfo file_0 37 2 37 23.
  Definition loc_3 : location_info := LocationInfo file_0 43 2 46 3.
  Definition loc_4 : location_info := LocationInfo file_0 47 2 47 24.
  Definition loc_5 : location_info := LocationInfo file_0 48 2 48 19.
  Definition loc_6 : location_info := LocationInfo file_0 48 20 48 39.
  Definition loc_7 : location_info := LocationInfo file_0 49 2 49 15.
  Definition loc_8 : location_info := LocationInfo file_0 49 2 49 6.
  Definition loc_9 : location_info := LocationInfo file_0 49 3 49 6.
  Definition loc_10 : location_info := LocationInfo file_0 49 3 49 6.
  Definition loc_11 : location_info := LocationInfo file_0 49 9 49 14.
  Definition loc_12 : location_info := LocationInfo file_0 49 9 49 14.
  Definition loc_13 : location_info := LocationInfo file_0 48 20 48 31.
  Definition loc_14 : location_info := LocationInfo file_0 48 20 48 25.
  Definition loc_15 : location_info := LocationInfo file_0 48 20 48 25.
  Definition loc_16 : location_info := LocationInfo file_0 48 34 48 38.
  Definition loc_17 : location_info := LocationInfo file_0 48 34 48 38.
  Definition loc_18 : location_info := LocationInfo file_0 48 35 48 38.
  Definition loc_19 : location_info := LocationInfo file_0 48 35 48 38.
  Definition loc_20 : location_info := LocationInfo file_0 48 2 48 13.
  Definition loc_21 : location_info := LocationInfo file_0 48 2 48 7.
  Definition loc_22 : location_info := LocationInfo file_0 48 2 48 7.
  Definition loc_23 : location_info := LocationInfo file_0 48 16 48 18.
  Definition loc_24 : location_info := LocationInfo file_0 48 16 48 18.
  Definition loc_25 : location_info := LocationInfo file_0 47 19 47 23.
  Definition loc_26 : location_info := LocationInfo file_0 47 19 47 23.
  Definition loc_29 : location_info := LocationInfo file_0 43 2 46 3.
  Definition loc_30 : location_info := LocationInfo file_0 43 32 46 3.
  Definition loc_31 : location_info := LocationInfo file_0 44 4 44 33.
  Definition loc_32 : location_info := LocationInfo file_0 45 4 45 24.
  Definition loc_33 : location_info := LocationInfo file_0 43 2 46 3.
  Definition loc_34 : location_info := LocationInfo file_0 43 2 46 3.
  Definition loc_35 : location_info := LocationInfo file_0 45 4 45 7.
  Definition loc_36 : location_info := LocationInfo file_0 45 10 45 23.
  Definition loc_37 : location_info := LocationInfo file_0 45 11 45 23.
  Definition loc_38 : location_info := LocationInfo file_0 45 11 45 17.
  Definition loc_39 : location_info := LocationInfo file_0 45 11 45 17.
  Definition loc_40 : location_info := LocationInfo file_0 45 13 45 16.
  Definition loc_41 : location_info := LocationInfo file_0 45 13 45 16.
  Definition loc_42 : location_info := LocationInfo file_0 44 27 44 33.
  Definition loc_44 : location_info := LocationInfo file_0 44 7 44 25.
  Definition loc_45 : location_info := LocationInfo file_0 44 7 44 9.
  Definition loc_46 : location_info := LocationInfo file_0 44 7 44 9.
  Definition loc_47 : location_info := LocationInfo file_0 44 13 44 25.
  Definition loc_48 : location_info := LocationInfo file_0 44 13 44 25.
  Definition loc_49 : location_info := LocationInfo file_0 44 13 44 19.
  Definition loc_50 : location_info := LocationInfo file_0 44 13 44 19.
  Definition loc_51 : location_info := LocationInfo file_0 44 15 44 18.
  Definition loc_52 : location_info := LocationInfo file_0 44 15 44 18.
  Definition loc_53 : location_info := LocationInfo file_0 43 8 43 30.
  Definition loc_54 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_55 : location_info := LocationInfo file_0 43 8 43 12.
  Definition loc_56 : location_info := LocationInfo file_0 43 9 43 12.
  Definition loc_57 : location_info := LocationInfo file_0 43 9 43 12.
  Definition loc_58 : location_info := LocationInfo file_0 43 16 43 30.
  Definition loc_59 : location_info := LocationInfo file_0 37 18 37 22.
  Definition loc_60 : location_info := LocationInfo file_0 37 18 37 22.

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

  (* Definition of struct [chunk]. *)
  Program Definition struct_chunk := {|
    sl_members := [
      (Some "size", it_layout size_t);
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [free]. *)
  Definition impl_free : function := {|
    f_args := [
      ("list", void*);
      ("data", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("cur", void*);
      ("entry", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "cur" <-{ void* }
          LocInfoE loc_59 (use{void*} (LocInfoE loc_60 ("list"))) ;
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_53 ;
        if: LocInfoE loc_53 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_53 ((LocInfoE loc_54 (use{void*} (LocInfoE loc_56 (!{void*} (LocInfoE loc_57 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_58 (NULL)))))
        then
        locinfo: loc_44 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_44 ;
        if: LocInfoE loc_44 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_44 ((LocInfoE loc_45 (use{it_layout size_t} (LocInfoE loc_46 ("sz")))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ((LocInfoE loc_49 (!{void*} (LocInfoE loc_51 (!{void*} (LocInfoE loc_52 ("cur")))))) at{struct_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_32 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        "entry" <-{ void* }
          LocInfoE loc_25 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_25 (use{void*} (LocInfoE loc_26 ("data"))))) ;
        locinfo: loc_5 ;
        LocInfoE loc_20 ((LocInfoE loc_21 (!{void*} (LocInfoE loc_22 ("entry")))) at{struct_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_23 (use{it_layout size_t} (LocInfoE loc_24 ("sz"))) ;
        locinfo: loc_6 ;
        LocInfoE loc_13 ((LocInfoE loc_14 (!{void*} (LocInfoE loc_15 ("entry")))) at{struct_chunk} "next") <-{ void* }
          LocInfoE loc_16 (use{void*} (LocInfoE loc_18 (!{void*} (LocInfoE loc_19 ("cur"))))) ;
        locinfo: loc_7 ;
        LocInfoE loc_9 (!{void*} (LocInfoE loc_10 ("cur"))) <-{ void* }
          LocInfoE loc_11 (use{void*} (LocInfoE loc_12 ("entry"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_32 ;
        LocInfoE loc_35 ("cur") <-{ void* }
          LocInfoE loc_36 (&(LocInfoE loc_37 ((LocInfoE loc_38 (!{void*} (LocInfoE loc_40 (!{void*} (LocInfoE loc_41 ("cur")))))) at{struct_chunk} "next"))) ;
        locinfo: loc_33 ;
        Goto "continue2"
      ]> $
      <[ "#5" :=
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_32 ;
        Goto "#4"
      ]> $
      <[ "continue2" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
