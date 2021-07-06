From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/ocaml_runtime.c]. *)
Section code.
  Definition file_0 : string := "examples/ocaml_runtime.c".
  Definition loc_2 : location_info := LocationInfo file_0 29 2 29 39.
  Definition loc_3 : location_info := LocationInfo file_0 30 2 30 30.
  Definition loc_4 : location_info := LocationInfo file_0 32 2 32 32.
  Definition loc_5 : location_info := LocationInfo file_0 33 2 33 57.
  Definition loc_6 : location_info := LocationInfo file_0 35 2 35 28.
  Definition loc_7 : location_info := LocationInfo file_0 36 2 36 28.
  Definition loc_8 : location_info := LocationInfo file_0 38 2 38 54.
  Definition loc_9 : location_info := LocationInfo file_0 39 2 39 28.
  Definition loc_10 : location_info := LocationInfo file_0 40 2 40 39.
  Definition loc_11 : location_info := LocationInfo file_0 40 9 40 37.
  Definition loc_12 : location_info := LocationInfo file_0 40 9 40 23.
  Definition loc_13 : location_info := LocationInfo file_0 40 9 40 23.
  Definition loc_14 : location_info := LocationInfo file_0 40 10 40 23.
  Definition loc_15 : location_info := LocationInfo file_0 40 10 40 23.
  Definition loc_16 : location_info := LocationInfo file_0 40 27 40 37.
  Definition loc_17 : location_info := LocationInfo file_0 39 9 39 26.
  Definition loc_18 : location_info := LocationInfo file_0 39 9 39 20.
  Definition loc_19 : location_info := LocationInfo file_0 39 10 39 14.
  Definition loc_20 : location_info := LocationInfo file_0 39 10 39 14.
  Definition loc_21 : location_info := LocationInfo file_0 39 18 39 19.
  Definition loc_22 : location_info := LocationInfo file_0 39 24 39 26.
  Definition loc_23 : location_info := LocationInfo file_0 38 33 38 53.
  Definition loc_24 : location_info := LocationInfo file_0 38 51 38 53.
  Definition loc_25 : location_info := LocationInfo file_0 38 51 38 53.
  Definition loc_28 : location_info := LocationInfo file_0 36 9 36 26.
  Definition loc_29 : location_info := LocationInfo file_0 36 10 36 20.
  Definition loc_30 : location_info := LocationInfo file_0 36 11 36 15.
  Definition loc_31 : location_info := LocationInfo file_0 36 11 36 15.
  Definition loc_32 : location_info := LocationInfo file_0 36 18 36 19.
  Definition loc_33 : location_info := LocationInfo file_0 36 24 36 25.
  Definition loc_34 : location_info := LocationInfo file_0 35 9 35 26.
  Definition loc_35 : location_info := LocationInfo file_0 35 10 35 20.
  Definition loc_36 : location_info := LocationInfo file_0 35 11 35 15.
  Definition loc_37 : location_info := LocationInfo file_0 35 11 35 15.
  Definition loc_38 : location_info := LocationInfo file_0 35 18 35 19.
  Definition loc_39 : location_info := LocationInfo file_0 35 24 35 25.
  Definition loc_40 : location_info := LocationInfo file_0 33 13 33 56.
  Definition loc_41 : location_info := LocationInfo file_0 33 14 33 51.
  Definition loc_42 : location_info := LocationInfo file_0 33 22 33 51.
  Definition loc_43 : location_info := LocationInfo file_0 33 24 33 44.
  Definition loc_44 : location_info := LocationInfo file_0 33 33 33 44.
  Definition loc_45 : location_info := LocationInfo file_0 33 33 33 44.
  Definition loc_46 : location_info := LocationInfo file_0 33 48 33 49.
  Definition loc_47 : location_info := LocationInfo file_0 33 54 33 55.
  Definition loc_50 : location_info := LocationInfo file_0 32 13 32 31.
  Definition loc_51 : location_info := LocationInfo file_0 32 21 32 31.
  Definition loc_52 : location_info := LocationInfo file_0 32 22 32 31.
  Definition loc_55 : location_info := LocationInfo file_0 30 27 30 29.
  Definition loc_58 : location_info := LocationInfo file_0 29 28 29 38.

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
