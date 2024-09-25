From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/talk_demo_alloc.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/talk_demo_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 42 2 42 23.
  Definition loc_12 : location_info := LocationInfo file_1 43 2 43 15.
  Definition loc_13 : location_info := LocationInfo file_1 44 2 44 28.
  Definition loc_14 : location_info := LocationInfo file_1 44 9 44 27.
  Definition loc_15 : location_info := LocationInfo file_1 44 9 44 18.
  Definition loc_16 : location_info := LocationInfo file_1 44 9 44 18.
  Definition loc_17 : location_info := LocationInfo file_1 44 9 44 10.
  Definition loc_18 : location_info := LocationInfo file_1 44 9 44 10.
  Definition loc_19 : location_info := LocationInfo file_1 44 21 44 27.
  Definition loc_20 : location_info := LocationInfo file_1 44 21 44 27.
  Definition loc_21 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_22 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_23 : location_info := LocationInfo file_1 43 2 43 8.
  Definition loc_24 : location_info := LocationInfo file_1 43 2 43 3.
  Definition loc_25 : location_info := LocationInfo file_1 43 2 43 3.
  Definition loc_26 : location_info := LocationInfo file_1 43 2 43 14.
  Definition loc_27 : location_info := LocationInfo file_1 43 2 43 8.
  Definition loc_28 : location_info := LocationInfo file_1 43 2 43 8.
  Definition loc_29 : location_info := LocationInfo file_1 43 2 43 3.
  Definition loc_30 : location_info := LocationInfo file_1 43 2 43 3.
  Definition loc_31 : location_info := LocationInfo file_1 43 12 43 14.
  Definition loc_32 : location_info := LocationInfo file_1 43 12 43 14.
  Definition loc_33 : location_info := LocationInfo file_1 42 9 42 21.
  Definition loc_34 : location_info := LocationInfo file_1 42 9 42 11.
  Definition loc_35 : location_info := LocationInfo file_1 42 9 42 11.
  Definition loc_36 : location_info := LocationInfo file_1 42 15 42 21.
  Definition loc_37 : location_info := LocationInfo file_1 42 15 42 21.
  Definition loc_38 : location_info := LocationInfo file_1 42 15 42 16.
  Definition loc_39 : location_info := LocationInfo file_1 42 15 42 16.
  Definition loc_42 : location_info := LocationInfo file_1 51 2 51 24.
  Definition loc_43 : location_info := LocationInfo file_1 52 2 52 11.
  Definition loc_44 : location_info := LocationInfo file_1 52 12 52 21.
  Definition loc_45 : location_info := LocationInfo file_1 52 22 52 31.
  Definition loc_46 : location_info := LocationInfo file_1 53 2 53 18.
  Definition loc_47 : location_info := LocationInfo file_1 54 2 54 12.
  Definition loc_48 : location_info := LocationInfo file_1 54 9 54 11.
  Definition loc_49 : location_info := LocationInfo file_1 54 9 54 11.
  Definition loc_50 : location_info := LocationInfo file_1 54 10 54 11.
  Definition loc_51 : location_info := LocationInfo file_1 54 10 54 11.
  Definition loc_52 : location_info := LocationInfo file_1 53 12 53 17.
  Definition loc_53 : location_info := LocationInfo file_1 53 12 53 13.
  Definition loc_54 : location_info := LocationInfo file_1 53 12 53 13.
  Definition loc_55 : location_info := LocationInfo file_1 53 16 53 17.
  Definition loc_58 : location_info := LocationInfo file_1 52 22 52 26.
  Definition loc_59 : location_info := LocationInfo file_1 52 22 52 26.
  Definition loc_60 : location_info := LocationInfo file_1 52 22 52 23.
  Definition loc_61 : location_info := LocationInfo file_1 52 22 52 23.
  Definition loc_62 : location_info := LocationInfo file_1 52 24 52 25.
  Definition loc_63 : location_info := LocationInfo file_1 52 29 52 30.
  Definition loc_64 : location_info := LocationInfo file_1 52 12 52 16.
  Definition loc_65 : location_info := LocationInfo file_1 52 12 52 16.
  Definition loc_66 : location_info := LocationInfo file_1 52 12 52 13.
  Definition loc_67 : location_info := LocationInfo file_1 52 12 52 13.
  Definition loc_68 : location_info := LocationInfo file_1 52 14 52 15.
  Definition loc_69 : location_info := LocationInfo file_1 52 19 52 20.
  Definition loc_70 : location_info := LocationInfo file_1 52 2 52 6.
  Definition loc_71 : location_info := LocationInfo file_1 52 2 52 6.
  Definition loc_72 : location_info := LocationInfo file_1 52 2 52 3.
  Definition loc_73 : location_info := LocationInfo file_1 52 2 52 3.
  Definition loc_74 : location_info := LocationInfo file_1 52 4 52 5.
  Definition loc_75 : location_info := LocationInfo file_1 52 9 52 10.
  Definition loc_76 : location_info := LocationInfo file_1 51 12 51 23.
  Definition loc_77 : location_info := LocationInfo file_1 51 12 51 17.
  Definition loc_78 : location_info := LocationInfo file_1 51 12 51 17.
  Definition loc_79 : location_info := LocationInfo file_1 51 18 51 19.
  Definition loc_80 : location_info := LocationInfo file_1 51 18 51 19.
  Definition loc_81 : location_info := LocationInfo file_1 51 21 51 22.

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

  (* Definition of struct [spinlock]. *)
  Program Definition struct_spinlock := {|
    sl_members := [
      (Some "lock", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mem_t]. *)
  Program Definition struct_mem_t := {|
    sl_members := [
      (Some "len", it_layout size_t);
      (Some "buffer", void*)
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

  (* Definition of function [alloc]. *)
  Definition impl_alloc : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        assert{IntOp i32}: (LocInfoE loc_33 ((LocInfoE loc_34 (use{IntOp size_t} (LocInfoE loc_35 ("sz")))) ≤{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_36 (use{IntOp size_t} (LocInfoE loc_37 ((LocInfoE loc_38 (!{PtrOp} (LocInfoE loc_39 ("d")))) at{struct_mem_t} "len")))))) ;
        locinfo: loc_12 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp size_t} (LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_31 (use{IntOp size_t} (LocInfoE loc_32 ("sz"))))) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 ((LocInfoE loc_15 (use{PtrOp} (LocInfoE loc_16 ((LocInfoE loc_17 (!{PtrOp} (LocInfoE loc_18 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_19 (use{IntOp size_t} (LocInfoE loc_20 ((LocInfoE loc_21 (!{PtrOp} (LocInfoE loc_22 ("d")))) at{struct_mem_t} "len"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [client]. *)
  Definition impl_client (global_alloc : loc): function := {|
    f_args := [
      ("d", void*)
    ];
    f_local_vars := [
      ("x", void*);
      ("a", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "a" <-{ PtrOp }
          LocInfoE loc_76 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_76 (Call (LocInfoE loc_78 (global_alloc)) [@{expr} LocInfoE loc_79 (use{PtrOp} (LocInfoE loc_80 ("d"))) ;
          LocInfoE loc_81 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_81 (i2v 3 i32))) ]))) ;
        locinfo: loc_43 ;
        LocInfoE loc_71 ((LocInfoE loc_72 (!{PtrOp} (LocInfoE loc_73 ("a")))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_74 (i2v 0 i32))) <-{ IntOp u8 }
          LocInfoE loc_75 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_75 (i2v 0 i32))) ;
        locinfo: loc_44 ;
        LocInfoE loc_65 ((LocInfoE loc_66 (!{PtrOp} (LocInfoE loc_67 ("a")))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_68 (i2v 1 i32))) <-{ IntOp u8 }
          LocInfoE loc_69 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_69 (i2v 1 i32))) ;
        locinfo: loc_45 ;
        LocInfoE loc_59 ((LocInfoE loc_60 (!{PtrOp} (LocInfoE loc_61 ("a")))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_62 (i2v 2 i32))) <-{ IntOp u8 }
          LocInfoE loc_63 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_63 (i2v 2 i32))) ;
        "x" <-{ PtrOp }
          LocInfoE loc_52 ((LocInfoE loc_53 (use{PtrOp} (LocInfoE loc_54 ("a")))) at_offset{it_layout u8, PtrOp, IntOp i32} (LocInfoE loc_55 (i2v 2 i32))) ;
        locinfo: loc_47 ;
        Return (LocInfoE loc_48 (use{IntOp u8} (LocInfoE loc_50 (!{PtrOp} (LocInfoE loc_51 ("x"))))))
      ]> $∅
    )%E
  |}.
End code.
