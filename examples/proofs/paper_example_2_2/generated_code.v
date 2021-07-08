From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_2.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/paper_example_2_2.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 37 2 37 23.
  Definition loc_12 : location_info := LocationInfo file_1 43 2 46 3.
  Definition loc_13 : location_info := LocationInfo file_1 47 2 47 24.
  Definition loc_14 : location_info := LocationInfo file_1 48 2 48 19.
  Definition loc_15 : location_info := LocationInfo file_1 48 20 48 39.
  Definition loc_16 : location_info := LocationInfo file_1 49 2 49 15.
  Definition loc_17 : location_info := LocationInfo file_1 49 2 49 6.
  Definition loc_18 : location_info := LocationInfo file_1 49 3 49 6.
  Definition loc_19 : location_info := LocationInfo file_1 49 3 49 6.
  Definition loc_20 : location_info := LocationInfo file_1 49 9 49 14.
  Definition loc_21 : location_info := LocationInfo file_1 49 9 49 14.
  Definition loc_22 : location_info := LocationInfo file_1 48 20 48 31.
  Definition loc_23 : location_info := LocationInfo file_1 48 20 48 25.
  Definition loc_24 : location_info := LocationInfo file_1 48 20 48 25.
  Definition loc_25 : location_info := LocationInfo file_1 48 34 48 38.
  Definition loc_26 : location_info := LocationInfo file_1 48 34 48 38.
  Definition loc_27 : location_info := LocationInfo file_1 48 35 48 38.
  Definition loc_28 : location_info := LocationInfo file_1 48 35 48 38.
  Definition loc_29 : location_info := LocationInfo file_1 48 2 48 13.
  Definition loc_30 : location_info := LocationInfo file_1 48 2 48 7.
  Definition loc_31 : location_info := LocationInfo file_1 48 2 48 7.
  Definition loc_32 : location_info := LocationInfo file_1 48 16 48 18.
  Definition loc_33 : location_info := LocationInfo file_1 48 16 48 18.
  Definition loc_34 : location_info := LocationInfo file_1 47 19 47 23.
  Definition loc_35 : location_info := LocationInfo file_1 47 19 47 23.
  Definition loc_38 : location_info := LocationInfo file_1 43 2 46 3.
  Definition loc_39 : location_info := LocationInfo file_1 43 32 46 3.
  Definition loc_40 : location_info := LocationInfo file_1 44 4 44 33.
  Definition loc_41 : location_info := LocationInfo file_1 45 4 45 24.
  Definition loc_42 : location_info := LocationInfo file_1 43 2 46 3.
  Definition loc_43 : location_info := LocationInfo file_1 43 2 46 3.
  Definition loc_44 : location_info := LocationInfo file_1 45 4 45 7.
  Definition loc_45 : location_info := LocationInfo file_1 45 10 45 23.
  Definition loc_46 : location_info := LocationInfo file_1 45 11 45 23.
  Definition loc_47 : location_info := LocationInfo file_1 45 11 45 17.
  Definition loc_48 : location_info := LocationInfo file_1 45 11 45 17.
  Definition loc_49 : location_info := LocationInfo file_1 45 13 45 16.
  Definition loc_50 : location_info := LocationInfo file_1 45 13 45 16.
  Definition loc_51 : location_info := LocationInfo file_1 44 27 44 33.
  Definition loc_53 : location_info := LocationInfo file_1 44 7 44 25.
  Definition loc_54 : location_info := LocationInfo file_1 44 7 44 9.
  Definition loc_55 : location_info := LocationInfo file_1 44 7 44 9.
  Definition loc_56 : location_info := LocationInfo file_1 44 13 44 25.
  Definition loc_57 : location_info := LocationInfo file_1 44 13 44 25.
  Definition loc_58 : location_info := LocationInfo file_1 44 13 44 19.
  Definition loc_59 : location_info := LocationInfo file_1 44 13 44 19.
  Definition loc_60 : location_info := LocationInfo file_1 44 15 44 18.
  Definition loc_61 : location_info := LocationInfo file_1 44 15 44 18.
  Definition loc_62 : location_info := LocationInfo file_1 43 8 43 30.
  Definition loc_63 : location_info := LocationInfo file_1 43 8 43 12.
  Definition loc_64 : location_info := LocationInfo file_1 43 8 43 12.
  Definition loc_65 : location_info := LocationInfo file_1 43 9 43 12.
  Definition loc_66 : location_info := LocationInfo file_1 43 9 43 12.
  Definition loc_67 : location_info := LocationInfo file_1 43 16 43 30.
  Definition loc_68 : location_info := LocationInfo file_1 37 18 37 22.
  Definition loc_69 : location_info := LocationInfo file_1 37 18 37 22.

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

  (* Definition of function [copy_alloc_id]. *)
  Definition impl_copy_alloc_id : function := {|
    f_args := [
      ("to", it_layout uintptr_t);
      ("from", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

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
          LocInfoE loc_68 (use{void*} (LocInfoE loc_69 ("list"))) ;
        locinfo: loc_12 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_62 ;
        if: LocInfoE loc_62 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_62 ((LocInfoE loc_63 (use{void*} (LocInfoE loc_65 (!{void*} (LocInfoE loc_66 ("cur")))))) !={PtrOp, PtrOp} (LocInfoE loc_67 (NULL)))))
        then
        locinfo: loc_53 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_53 ;
        if: LocInfoE loc_53 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_53 ((LocInfoE loc_54 (use{it_layout size_t} (LocInfoE loc_55 ("sz")))) ≤{IntOp size_t, IntOp size_t} (LocInfoE loc_56 (use{it_layout size_t} (LocInfoE loc_57 ((LocInfoE loc_58 (!{void*} (LocInfoE loc_60 (!{void*} (LocInfoE loc_61 ("cur")))))) at{struct_chunk} "size")))))))
        then
        Goto "#5"
        else
        locinfo: loc_41 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        "entry" <-{ void* }
          LocInfoE loc_34 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_34 (use{void*} (LocInfoE loc_35 ("data"))))) ;
        locinfo: loc_14 ;
        LocInfoE loc_29 ((LocInfoE loc_30 (!{void*} (LocInfoE loc_31 ("entry")))) at{struct_chunk} "size") <-{ it_layout size_t }
          LocInfoE loc_32 (use{it_layout size_t} (LocInfoE loc_33 ("sz"))) ;
        locinfo: loc_15 ;
        LocInfoE loc_22 ((LocInfoE loc_23 (!{void*} (LocInfoE loc_24 ("entry")))) at{struct_chunk} "next") <-{ void* }
          LocInfoE loc_25 (use{void*} (LocInfoE loc_27 (!{void*} (LocInfoE loc_28 ("cur"))))) ;
        locinfo: loc_16 ;
        LocInfoE loc_18 (!{void*} (LocInfoE loc_19 ("cur"))) <-{ void* }
          LocInfoE loc_20 (use{void*} (LocInfoE loc_21 ("entry"))) ;
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_41 ;
        LocInfoE loc_44 ("cur") <-{ void* }
          LocInfoE loc_45 (&(LocInfoE loc_46 ((LocInfoE loc_47 (!{void*} (LocInfoE loc_49 (!{void*} (LocInfoE loc_50 ("cur")))))) at{struct_chunk} "next"))) ;
        locinfo: loc_42 ;
        Goto "continue4"
      ]> $
      <[ "#5" :=
        Goto "#3"
      ]> $
      <[ "#6" :=
        locinfo: loc_41 ;
        Goto "#4"
      ]> $
      <[ "continue4" :=
        locinfo: loc_12 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
