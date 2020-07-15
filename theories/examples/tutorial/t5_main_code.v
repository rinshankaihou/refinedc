From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/t5_main.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/t5_main.c".
  Definition loc_2 : location_info := LocationInfo file_0 11 4 11 17.
  Definition loc_3 : location_info := LocationInfo file_0 12 4 12 32.
  Definition loc_4 : location_info := LocationInfo file_0 14 4 14 11.
  Definition loc_5 : location_info := LocationInfo file_0 15 4 15 13.
  Definition loc_6 : location_info := LocationInfo file_0 15 11 15 12.
  Definition loc_7 : location_info := LocationInfo file_0 14 4 14 8.
  Definition loc_8 : location_info := LocationInfo file_0 14 4 14 8.
  Definition loc_9 : location_info := LocationInfo file_0 12 4 12 8.
  Definition loc_10 : location_info := LocationInfo file_0 12 4 12 8.
  Definition loc_11 : location_info := LocationInfo file_0 12 9 12 14.
  Definition loc_12 : location_info := LocationInfo file_0 12 16 12 30.
  Definition loc_13 : location_info := LocationInfo file_0 12 16 12 30.
  Definition loc_14 : location_info := LocationInfo file_0 11 4 11 14.
  Definition loc_15 : location_info := LocationInfo file_0 11 4 11 14.

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
  Definition impl_main (allocator_data test free init_alloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        "_" <- LocInfoE loc_15 (init_alloc) with [  ] ;
        locinfo: loc_3 ;
        "_" <- LocInfoE loc_10 (free) with
          [ LocInfoE loc_11 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_11 (i2v 10000 i32))) ;
          LocInfoE loc_12 (&(LocInfoE loc_13 (allocator_data))) ] ;
        locinfo: loc_4 ;
        "_" <- LocInfoE loc_8 (test) with [  ] ;
        locinfo: loc_5 ;
        Return (LocInfoE loc_6 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
