From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/container_of.c]. *)
Section code.
  Definition file_0 : string := "examples/container_of.c".
  Definition loc_2 : location_info := LocationInfo file_0 11 2 11 35.
  Definition loc_3 : location_info := LocationInfo file_0 12 2 12 16.
  Definition loc_4 : location_info := LocationInfo file_0 13 2 13 9.
  Definition loc_5 : location_info := LocationInfo file_0 14 2 14 77.
  Definition loc_6 : location_info := LocationInfo file_0 15 2 15 12.
  Definition loc_7 : location_info := LocationInfo file_0 16 2 16 13.
  Definition loc_8 : location_info := LocationInfo file_0 16 9 16 12.
  Definition loc_9 : location_info := LocationInfo file_0 16 9 16 12.
  Definition loc_10 : location_info := LocationInfo file_0 16 9 16 10.
  Definition loc_11 : location_info := LocationInfo file_0 15 2 15 7.
  Definition loc_12 : location_info := LocationInfo file_0 15 2 15 4.
  Definition loc_13 : location_info := LocationInfo file_0 15 2 15 4.
  Definition loc_14 : location_info := LocationInfo file_0 15 10 15 11.
  Definition loc_15 : location_info := LocationInfo file_0 14 20 14 76.
  Definition loc_16 : location_info := LocationInfo file_0 14 35 14 76.
  Definition loc_17 : location_info := LocationInfo file_0 14 37 14 48.
  Definition loc_18 : location_info := LocationInfo file_0 14 45 14 48.
  Definition loc_19 : location_info := LocationInfo file_0 14 45 14 48.
  Definition loc_20 : location_info := LocationInfo file_0 14 51 14 74.
  Definition loc_23 : location_info := LocationInfo file_0 13 2 13 4.
  Definition loc_24 : location_info := LocationInfo file_0 13 3 13 4.
  Definition loc_25 : location_info := LocationInfo file_0 13 3 13 4.
  Definition loc_26 : location_info := LocationInfo file_0 13 7 13 8.
  Definition loc_27 : location_info := LocationInfo file_0 12 11 12 15.
  Definition loc_28 : location_info := LocationInfo file_0 12 12 12 15.
  Definition loc_29 : location_info := LocationInfo file_0 12 12 12 13.
  Definition loc_33 : location_info := LocationInfo file_0 11 24 11 25.
  Definition loc_34 : location_info := LocationInfo file_0 11 32 11 33.

  (* Definition of struct [test]. *)
  Program Definition struct_test := {|
    sl_members := [
      (Some "a", it_layout i32);
      (Some "b", it_layout i32)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [container_of_test]. *)
  Definition impl_container_of_test : function := {|
    f_args := [
    ];
    f_local_vars := [
      ("b", void*);
      ("t", layout_of struct_test);
      ("pt", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "t" <-{ layout_of struct_test }
          StructInit struct_test [
            ("a", LocInfoE loc_33 (i2v 1 i32) : expr) ;
            ("b", LocInfoE loc_34 (i2v 2 i32) : expr)
          ] ;
        "b" <-{ void* }
          LocInfoE loc_27 (&(LocInfoE loc_28 ((LocInfoE loc_29 ("t")) at{struct_test} "b"))) ;
        locinfo: loc_4 ;
        LocInfoE loc_24 (!{void*} (LocInfoE loc_25 ("b"))) <-{ it_layout i32 }
          LocInfoE loc_26 (i2v 3 i32) ;
        "pt" <-{ void* }
          LocInfoE loc_15 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_16 ((LocInfoE loc_17 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_18 (use{void*} (LocInfoE loc_19 ("b")))))) at_neg_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_20 ((OffsetOf (struct_test) ("b"))))))) ;
        locinfo: loc_6 ;
        LocInfoE loc_11 ((LocInfoE loc_12 (!{void*} (LocInfoE loc_13 ("pt")))) at{struct_test} "a") <-{ it_layout i32 }
          LocInfoE loc_14 (i2v 4 i32) ;
        locinfo: loc_7 ;
        Return (LocInfoE loc_8 (use{it_layout i32} (LocInfoE loc_9 ((LocInfoE loc_10 ("t")) at{struct_test} "a"))))
      ]> $∅
    )%E
  |}.
End code.
