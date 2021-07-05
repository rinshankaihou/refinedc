From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section code.
  Definition file_0 : string := "examples/ocaml_runtime.c".
  Definition loc_2 : location_info := LocationInfo file_0 46 2 46 39.
  Definition loc_3 : location_info := LocationInfo file_0 47 2 47 30.
  Definition loc_4 : location_info := LocationInfo file_0 49 2 49 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 2 50 57.
  Definition loc_6 : location_info := LocationInfo file_0 52 2 52 28.
  Definition loc_7 : location_info := LocationInfo file_0 53 2 53 28.
  Definition loc_8 : location_info := LocationInfo file_0 55 2 55 54.
  Definition loc_9 : location_info := LocationInfo file_0 56 2 56 28.
  Definition loc_10 : location_info := LocationInfo file_0 57 2 57 39.
  Definition loc_11 : location_info := LocationInfo file_0 57 9 57 37.
  Definition loc_12 : location_info := LocationInfo file_0 57 9 57 23.
  Definition loc_13 : location_info := LocationInfo file_0 57 9 57 23.
  Definition loc_14 : location_info := LocationInfo file_0 57 10 57 23.
  Definition loc_15 : location_info := LocationInfo file_0 57 10 57 23.
  Definition loc_16 : location_info := LocationInfo file_0 57 27 57 37.
  Definition loc_17 : location_info := LocationInfo file_0 56 9 56 26.
  Definition loc_18 : location_info := LocationInfo file_0 56 9 56 20.
  Definition loc_19 : location_info := LocationInfo file_0 56 10 56 14.
  Definition loc_20 : location_info := LocationInfo file_0 56 10 56 14.
  Definition loc_21 : location_info := LocationInfo file_0 56 18 56 19.
  Definition loc_22 : location_info := LocationInfo file_0 56 24 56 26.
  Definition loc_23 : location_info := LocationInfo file_0 55 33 55 53.
  Definition loc_24 : location_info := LocationInfo file_0 55 51 55 53.
  Definition loc_25 : location_info := LocationInfo file_0 55 51 55 53.
  Definition loc_28 : location_info := LocationInfo file_0 53 9 53 26.
  Definition loc_29 : location_info := LocationInfo file_0 53 10 53 20.
  Definition loc_30 : location_info := LocationInfo file_0 53 11 53 15.
  Definition loc_31 : location_info := LocationInfo file_0 53 11 53 15.
  Definition loc_32 : location_info := LocationInfo file_0 53 18 53 19.
  Definition loc_33 : location_info := LocationInfo file_0 53 24 53 25.
  Definition loc_34 : location_info := LocationInfo file_0 52 9 52 26.
  Definition loc_35 : location_info := LocationInfo file_0 52 10 52 20.
  Definition loc_36 : location_info := LocationInfo file_0 52 11 52 15.
  Definition loc_37 : location_info := LocationInfo file_0 52 11 52 15.
  Definition loc_38 : location_info := LocationInfo file_0 52 18 52 19.
  Definition loc_39 : location_info := LocationInfo file_0 52 24 52 25.
  Definition loc_40 : location_info := LocationInfo file_0 50 13 50 56.
  Definition loc_41 : location_info := LocationInfo file_0 50 14 50 51.
  Definition loc_42 : location_info := LocationInfo file_0 50 22 50 51.
  Definition loc_43 : location_info := LocationInfo file_0 50 24 50 44.
  Definition loc_44 : location_info := LocationInfo file_0 50 33 50 44.
  Definition loc_45 : location_info := LocationInfo file_0 50 33 50 44.
  Definition loc_46 : location_info := LocationInfo file_0 50 48 50 49.
  Definition loc_47 : location_info := LocationInfo file_0 50 54 50 55.
  Definition loc_50 : location_info := LocationInfo file_0 49 13 49 31.
  Definition loc_51 : location_info := LocationInfo file_0 49 21 49 31.
  Definition loc_52 : location_info := LocationInfo file_0 49 22 49 31.
  Definition loc_55 : location_info := LocationInfo file_0 47 27 47 29.
  Definition loc_58 : location_info := LocationInfo file_0 46 28 46 38.

  (* Definition of function [client]. *)
  Definition impl_client : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("small_int", it_layout u32);
      ("large_int", it_layout u64);
      ("large_int_ptr", void*);
      ("v2", it_layout u64);
      ("v1", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "large_int" <-{ it_layout u64 }
          LocInfoE loc_58 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_58 (i2v 3735928559 u32))) ;
        "small_int" <-{ it_layout u32 }
          LocInfoE loc_55 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_55 (i2v 42 i32))) ;
        "v1" <-{ it_layout u64 }
          LocInfoE loc_50 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_51 (&(LocInfoE loc_52 ("large_int"))))) ;
        "v2" <-{ it_layout u64 }
          LocInfoE loc_40 ((LocInfoE loc_41 (UnOp (CastOp $ IntOp u64) (IntOp u64) (LocInfoE loc_42 ((LocInfoE loc_43 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_44 (use{it_layout u32} (LocInfoE loc_45 ("small_int")))))) <<{IntOp u64, IntOp u64} (LocInfoE loc_46 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_46 (i2v 1 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_47 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_47 (i2v 1 i32))))) ;
        locinfo: loc_6 ;
        assert: (LocInfoE loc_34 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_34 ((LocInfoE loc_35 ((LocInfoE loc_36 (use{it_layout u64} (LocInfoE loc_37 ("v1")))) &{IntOp u64, IntOp u64} (LocInfoE loc_38 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_38 (i2v 1 i32)))))) ={IntOp u64, IntOp u64} (LocInfoE loc_39 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_39 (i2v 0 i32)))))))) ;
        locinfo: loc_7 ;
        assert: (LocInfoE loc_28 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_28 ((LocInfoE loc_29 ((LocInfoE loc_30 (use{it_layout u64} (LocInfoE loc_31 ("v2")))) &{IntOp u64, IntOp u64} (LocInfoE loc_32 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_32 (i2v 1 i32)))))) !={IntOp u64, IntOp u64} (LocInfoE loc_33 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_33 (i2v 0 i32)))))))) ;
        "large_int_ptr" <-{ void* }
          LocInfoE loc_23 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_24 (use{it_layout u64} (LocInfoE loc_25 ("v1"))))) ;
        locinfo: loc_9 ;
        assert: (LocInfoE loc_17 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_17 ((LocInfoE loc_18 ((LocInfoE loc_19 (use{it_layout u64} (LocInfoE loc_20 ("v2")))) >>{IntOp u64, IntOp u64} (LocInfoE loc_21 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_21 (i2v 1 i32)))))) ={IntOp u64, IntOp u64} (LocInfoE loc_22 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_22 (i2v 42 i32)))))))) ;
        locinfo: loc_10 ;
        assert: (LocInfoE loc_11 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_11 ((LocInfoE loc_12 (use{it_layout u64} (LocInfoE loc_14 (!{void*} (LocInfoE loc_15 ("large_int_ptr")))))) ={IntOp u64, IntOp u64} (LocInfoE loc_16 (UnOp (CastOp $ IntOp u64) (IntOp u32) (LocInfoE loc_16 (i2v 3735928559 u32)))))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
