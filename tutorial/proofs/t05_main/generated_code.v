From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t05_main.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t05_main.c".
  Definition loc_2 : location_info := LocationInfo file_0 16 4 16 18.
  Definition loc_3 : location_info := LocationInfo file_0 17 4 17 33.
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
  Definition loc_14 : location_info := LocationInfo file_0 17 4 17 9.
  Definition loc_15 : location_info := LocationInfo file_0 17 4 17 9.
  Definition loc_16 : location_info := LocationInfo file_0 17 10 17 15.
  Definition loc_17 : location_info := LocationInfo file_0 17 17 17 31.
  Definition loc_18 : location_info := LocationInfo file_0 17 17 17 31.
  Definition loc_19 : location_info := LocationInfo file_0 16 4 16 15.
  Definition loc_20 : location_info := LocationInfo file_0 16 4 16 15.
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

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [latch]. *)
  Program Definition struct_latch := {|
    sl_members := [
      (Some "released", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [alloc_entry]. *)
  Program Definition struct_alloc_entry := {|
    sl_members := [
      (Some "size", it_layout size_t);
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [alloc_state]. *)
  Program Definition struct_alloc_state := {|
    sl_members := [
      (Some "lock", layout_of struct_spinlock);
      (None, Layout 7%nat 0%nat);
      (Some "data", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [main]. *)
  Definition impl_main (global_allocator_data global_initialized global_init_talloc global_latch_release global_test global_tfree : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        expr: (LocInfoE loc_2 (Call (LocInfoE loc_20 (global_init_talloc)) [@{expr}  ])) ;
        locinfo: loc_3 ;
        expr: (LocInfoE loc_3 (Call (LocInfoE loc_15 (global_tfree)) [@{expr} LocInfoE loc_16 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_16 (i2v 10000 i32))) ;
        LocInfoE loc_17 (&(LocInfoE loc_18 (global_allocator_data))) ])) ;
        locinfo: loc_4 ;
        expr: (LocInfoE loc_4 (Call (LocInfoE loc_11 (global_latch_release)) [@{expr} LocInfoE loc_12 (&(LocInfoE loc_13 (global_initialized))) ])) ;
        locinfo: loc_5 ;
        expr: (LocInfoE loc_5 (Call (LocInfoE loc_9 (global_test)) [@{expr}  ])) ;
        locinfo: loc_6 ;
        Return (LocInfoE loc_7 (i2v 0 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [main2]. *)
  Definition impl_main2 (global_initialized global_latch_wait global_test : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_23 ;
        expr: (LocInfoE loc_23 (Call (LocInfoE loc_30 (global_latch_wait)) [@{expr} LocInfoE loc_31 (&(LocInfoE loc_32 (global_initialized))) ])) ;
        locinfo: loc_24 ;
        expr: (LocInfoE loc_24 (Call (LocInfoE loc_28 (global_test)) [@{expr}  ])) ;
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
