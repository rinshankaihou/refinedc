From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/lithium.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/lithium.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 14 2 18 3.
  Definition loc_12 : location_info := LocationInfo file_1 14 27 16 3.
  Definition loc_13 : location_info := LocationInfo file_1 15 4 15 18.
  Definition loc_14 : location_info := LocationInfo file_1 15 11 15 17.
  Definition loc_15 : location_info := LocationInfo file_1 15 11 15 13.
  Definition loc_16 : location_info := LocationInfo file_1 15 11 15 13.
  Definition loc_17 : location_info := LocationInfo file_1 15 12 15 13.
  Definition loc_18 : location_info := LocationInfo file_1 15 12 15 13.
  Definition loc_19 : location_info := LocationInfo file_1 15 16 15 17.
  Definition loc_20 : location_info := LocationInfo file_1 16 9 18 3.
  Definition loc_21 : location_info := LocationInfo file_1 17 4 17 13.
  Definition loc_22 : location_info := LocationInfo file_1 17 11 17 12.
  Definition loc_23 : location_info := LocationInfo file_1 14 6 14 25.
  Definition loc_24 : location_info := LocationInfo file_1 14 6 14 7.
  Definition loc_25 : location_info := LocationInfo file_1 14 6 14 7.
  Definition loc_26 : location_info := LocationInfo file_1 14 11 14 25.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [lithium_test]. *)
  Definition impl_lithium_test : function := {|
    f_args := [
      ("a", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_23 ;
        if{IntOp i32, None}: LocInfoE loc_23 ((LocInfoE loc_24 (use{PtrOp} (LocInfoE loc_25 ("a")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_26 (NULL)))
        then
        locinfo: loc_13 ;
          Goto "#1"
        else
        locinfo: loc_21 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 ((LocInfoE loc_15 (use{IntOp i32} (LocInfoE loc_17 (!{PtrOp} (LocInfoE loc_18 ("a")))))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (i2v 0 i32))))
      ]> $
      <[ "#2" :=
        locinfo: loc_21 ;
        Return (LocInfoE loc_22 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
