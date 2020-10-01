From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t05_main.c".
  Definition loc_2 : location_info := LocationInfo file_0 16 4 16 17.
  Definition loc_3 : location_info := LocationInfo file_0 17 4 17 32.
  Definition loc_4 : location_info := LocationInfo file_0 18 4 18 32.
  Definition loc_5 : location_info := LocationInfo file_0 20 4 20 11.
  Definition loc_6 : location_info := LocationInfo file_0 21 4 21 13.
  Definition loc_7 : location_info := LocationInfo file_0 21 11 21 12.
  Definition loc_8 : location_info := LocationInfo file_0 20 4 20 8.
  Definition loc_9 : location_info := LocationInfo file_0 20 4 20 8.
  Definition loc_10 : location_info := LocationInfo file_0 18 4 18 17.
  Definition loc_11 : location_info := LocationInfo file_0 18 4 18 17.
  Definition loc_12 : location_info := LocationInfo file_0 18 18 18 30.
  Definition loc_13 : location_info := LocationInfo file_0 18 19 18 30.
  Definition loc_14 : location_info := LocationInfo file_0 17 4 17 8.
  Definition loc_15 : location_info := LocationInfo file_0 17 4 17 8.
  Definition loc_16 : location_info := LocationInfo file_0 17 9 17 14.
  Definition loc_17 : location_info := LocationInfo file_0 17 16 17 30.
  Definition loc_18 : location_info := LocationInfo file_0 17 16 17 30.
  Definition loc_19 : location_info := LocationInfo file_0 16 4 16 14.
  Definition loc_20 : location_info := LocationInfo file_0 16 4 16 14.
  Definition loc_23 : location_info := LocationInfo file_0 27 4 27 29.
  Definition loc_24 : location_info := LocationInfo file_0 29 4 29 11.
  Definition loc_25 : location_info := LocationInfo file_0 30 4 30 13.
  Definition loc_26 : location_info := LocationInfo file_0 30 11 30 12.
  Definition loc_27 : location_info := LocationInfo file_0 29 4 29 8.
  Definition loc_28 : location_info := LocationInfo file_0 29 4 29 8.
  Definition loc_29 : location_info := LocationInfo file_0 27 4 27 14.
  Definition loc_30 : location_info := LocationInfo file_0 27 4 27 14.
  Definition loc_31 : location_info := LocationInfo file_0 27 15 27 27.
  Definition loc_32 : location_info := LocationInfo file_0 27 16 27 27.

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

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", it_layout bool_it)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [alloc_entry]. *)
  Program Definition struct_alloc_entry := {|
    sl_members := [
      (Some "size", it_layout size_t);
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [alloc_state]. *)
  Program Definition struct_alloc_state := {|
    sl_members := [
      (Some "lock", layout_of struct_spinlock);
      (None, mk_layout 7%nat 0%nat);
      (Some "data", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [main]. *)
  Definition impl_main (allocator_data initialized free init_alloc latch_release test : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        "_" <- LocInfoE loc_20 (init_alloc) with [  ] ;
        locinfo: loc_3 ;
        "_" <- LocInfoE loc_15 (free) with
          [ LocInfoE loc_16 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_16 (i2v 10000 i32))) ;
          LocInfoE loc_17 (&(LocInfoE loc_18 (allocator_data))) ] ;
        locinfo: loc_4 ;
        "_" <- LocInfoE loc_11 (latch_release) with
          [ LocInfoE loc_12 (&(LocInfoE loc_13 (initialized))) ] ;
        locinfo: loc_5 ;
        "_" <- LocInfoE loc_9 (test) with [  ] ;
        locinfo: loc_6 ;
        Return (LocInfoE loc_7 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [main2]. *)
  Definition impl_main2 (initialized latch_wait test : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_23 ;
        "_" <- LocInfoE loc_30 (latch_wait) with
          [ LocInfoE loc_31 (&(LocInfoE loc_32 (initialized))) ] ;
        locinfo: loc_24 ;
        "_" <- LocInfoE loc_28 (test) with [  ] ;
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
