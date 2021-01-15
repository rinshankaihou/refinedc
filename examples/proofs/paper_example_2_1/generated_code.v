From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section code.
  Definition file_0 : string := "examples/paper_example_2_1.c".
  Definition loc_2 : location_info := LocationInfo file_0 29 2 29 42.
  Definition loc_3 : location_info := LocationInfo file_0 30 2 30 17.
  Definition loc_4 : location_info := LocationInfo file_0 31 2 31 28.
  Definition loc_5 : location_info := LocationInfo file_0 31 9 31 27.
  Definition loc_6 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_7 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_8 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_9 : location_info := LocationInfo file_0 31 9 31 10.
  Definition loc_10 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_11 : location_info := LocationInfo file_0 31 21 31 27.
  Definition loc_12 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_13 : location_info := LocationInfo file_0 31 21 31 22.
  Definition loc_14 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_15 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_16 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_17 : location_info := LocationInfo file_0 30 2 30 16.
  Definition loc_18 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_19 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_20 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_21 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_22 : location_info := LocationInfo file_0 30 12 30 16.
  Definition loc_23 : location_info := LocationInfo file_0 30 12 30 16.
  Definition loc_24 : location_info := LocationInfo file_0 29 20 29 42.
  Definition loc_25 : location_info := LocationInfo file_0 29 27 29 41.
  Definition loc_27 : location_info := LocationInfo file_0 29 5 29 18.
  Definition loc_28 : location_info := LocationInfo file_0 29 5 29 9.
  Definition loc_29 : location_info := LocationInfo file_0 29 5 29 9.
  Definition loc_30 : location_info := LocationInfo file_0 29 12 29 18.
  Definition loc_31 : location_info := LocationInfo file_0 29 12 29 18.
  Definition loc_32 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_33 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_36 : location_info := LocationInfo file_0 49 2 49 17.
  Definition loc_37 : location_info := LocationInfo file_0 50 2 50 35.
  Definition loc_38 : location_info := LocationInfo file_0 50 35 50 3.
  Definition loc_39 : location_info := LocationInfo file_0 51 2 51 33.
  Definition loc_40 : location_info := LocationInfo file_0 52 2 52 19.
  Definition loc_41 : location_info := LocationInfo file_0 53 2 53 13.
  Definition loc_42 : location_info := LocationInfo file_0 53 9 53 12.
  Definition loc_43 : location_info := LocationInfo file_0 53 9 53 12.
  Definition loc_44 : location_info := LocationInfo file_0 52 2 52 11.
  Definition loc_45 : location_info := LocationInfo file_0 52 2 52 11.
  Definition loc_46 : location_info := LocationInfo file_0 52 12 52 17.
  Definition loc_47 : location_info := LocationInfo file_0 52 13 52 17.
  Definition loc_48 : location_info := LocationInfo file_0 51 14 51 32.
  Definition loc_49 : location_info := LocationInfo file_0 51 14 51 19.
  Definition loc_50 : location_info := LocationInfo file_0 51 14 51 19.
  Definition loc_51 : location_info := LocationInfo file_0 51 20 51 25.
  Definition loc_52 : location_info := LocationInfo file_0 51 21 51 25.
  Definition loc_53 : location_info := LocationInfo file_0 51 27 51 31.
  Definition loc_54 : location_info := LocationInfo file_0 51 27 51 31.
  Definition loc_57 : location_info := LocationInfo file_0 50 27 50 34.
  Definition loc_58 : location_info := LocationInfo file_0 50 28 50 34.
  Definition loc_59 : location_info := LocationInfo file_0 49 2 49 9.
  Definition loc_60 : location_info := LocationInfo file_0 49 2 49 9.
  Definition loc_61 : location_info := LocationInfo file_0 49 10 49 15.
  Definition loc_62 : location_info := LocationInfo file_0 49 11 49 15.
  Definition loc_65 : location_info := LocationInfo file_0 67 2 67 10.
  Definition loc_66 : location_info := LocationInfo file_0 67 2 67 4.
  Definition loc_67 : location_info := LocationInfo file_0 67 2 67 4.
  Definition loc_68 : location_info := LocationInfo file_0 67 2 67 4.
  Definition loc_69 : location_info := LocationInfo file_0 67 5 67 8.
  Definition loc_70 : location_info := LocationInfo file_0 67 5 67 8.
  Definition loc_73 : location_info := LocationInfo file_0 73 2 73 24.
  Definition loc_74 : location_info := LocationInfo file_0 74 2 74 30.
  Definition loc_75 : location_info := LocationInfo file_0 74 2 74 19.
  Definition loc_76 : location_info := LocationInfo file_0 74 2 74 19.
  Definition loc_77 : location_info := LocationInfo file_0 74 20 74 28.
  Definition loc_78 : location_info := LocationInfo file_0 74 20 74 28.
  Definition loc_79 : location_info := LocationInfo file_0 74 21 74 28.
  Definition loc_80 : location_info := LocationInfo file_0 74 21 74 28.
  Definition loc_81 : location_info := LocationInfo file_0 73 20 73 23.
  Definition loc_82 : location_info := LocationInfo file_0 73 20 73 23.
  Definition loc_87 : location_info := LocationInfo file_0 83 2 83 12.
  Definition loc_88 : location_info := LocationInfo file_0 84 2 84 47.
  Definition loc_89 : location_info := LocationInfo file_0 85 2 85 23.
  Definition loc_90 : location_info := LocationInfo file_0 85 2 85 19.
  Definition loc_91 : location_info := LocationInfo file_0 85 2 85 19.
  Definition loc_92 : location_info := LocationInfo file_0 85 20 85 21.
  Definition loc_93 : location_info := LocationInfo file_0 84 2 84 6.
  Definition loc_94 : location_info := LocationInfo file_0 84 2 84 6.
  Definition loc_95 : location_info := LocationInfo file_0 84 7 84 37.
  Definition loc_96 : location_info := LocationInfo file_0 84 39 84 45.
  Definition loc_97 : location_info := LocationInfo file_0 84 40 84 45.
  Definition loc_98 : location_info := LocationInfo file_0 83 2 83 7.
  Definition loc_99 : location_info := LocationInfo file_0 83 10 83 11.

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

  (* Definition of struct [mem_t]. *)
  Program Definition struct_mem_t := {|
    sl_members := [
      (Some "len", it_layout size_t);
      (Some "buffer", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [alloc]. *)
  Definition impl_alloc : function := {|
    f_args := [
      ("d", void*);
      ("size", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        if: LocInfoE loc_27 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_27 ((LocInfoE loc_28 (use{it_layout size_t} (LocInfoE loc_29 ("size")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_30 (use{it_layout size_t} (LocInfoE loc_31 ((LocInfoE loc_32 (!{void*} (LocInfoE loc_33 ("d")))) at{struct_mem_t} "len")))))))
        then
        locinfo: loc_24 ;
          Goto "#2"
        else
        locinfo: loc_3 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_3 ;
        LocInfoE loc_14 ((LocInfoE loc_15 (!{void*} (LocInfoE loc_16 ("d")))) at{struct_mem_t} "len") <-{ it_layout size_t }
          LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ((LocInfoE loc_20 (!{void*} (LocInfoE loc_21 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_22 (use{it_layout size_t} (LocInfoE loc_23 ("size"))))) ;
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 ((LocInfoE loc_6 (use{void*} (LocInfoE loc_7 ((LocInfoE loc_8 (!{void*} (LocInfoE loc_9 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_10 (use{it_layout size_t} (LocInfoE loc_11 ((LocInfoE loc_12 (!{void*} (LocInfoE loc_13 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_24 ;
        Return (LocInfoE loc_25 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [thread_safe_alloc]. *)
  Definition impl_thread_safe_alloc (global_data global_lock global_alloc global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_36 ;
        "_" <- LocInfoE loc_60 (global_sl_lock) with
          [ LocInfoE loc_61 (&(LocInfoE loc_62 (global_lock))) ] ;
        locinfo: loc_37 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_57 (&(LocInfoE loc_58 (global_data)))) ;
        locinfo: loc_48 ;
        "$0" <- LocInfoE loc_50 (global_alloc) with
          [ LocInfoE loc_51 (&(LocInfoE loc_52 (global_data))) ;
          LocInfoE loc_53 (use{it_layout size_t} (LocInfoE loc_54 ("size"))) ] ;
        "ret" <-{ void* } LocInfoE loc_48 ("$0") ;
        locinfo: loc_40 ;
        "_" <- LocInfoE loc_45 (global_sl_unlock) with
          [ LocInfoE loc_46 (AnnotExpr 1%nat LockA (LocInfoE loc_46 (&(LocInfoE loc_47 (global_lock))))) ] ;
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{void*} (LocInfoE loc_43 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [fork]. *)
  Definition impl_fork : function := {|
    f_args := [
      ("fn", void*);
      ("arg", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_65 ;
        "_" <- LocInfoE loc_67 (use{void*} (LocInfoE loc_68 ("fn"))) with
          [ LocInfoE loc_69 (use{void*} (LocInfoE loc_70 ("arg"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_thread_safe_alloc_fork_fn]. *)
  Definition impl_test_thread_safe_alloc_fork_fn (global_thread_safe_alloc : loc): function := {|
    f_args := [
      ("num", void*)
    ];
    f_local_vars := [
      ("num_int", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "num_int" <-{ void* }
          LocInfoE loc_81 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_81 (use{void*} (LocInfoE loc_82 ("num"))))) ;
        locinfo: loc_74 ;
        "_" <- LocInfoE loc_76 (global_thread_safe_alloc) with
          [ LocInfoE loc_77 (use{it_layout size_t} (LocInfoE loc_79 (!{void*} (LocInfoE loc_80 ("num_int"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_thread_safe_alloc]. *)
  Definition impl_test_thread_safe_alloc (global_param global_fork global_test_thread_safe_alloc_fork_fn global_thread_safe_alloc : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_87 ;
        LocInfoE loc_98 (global_param) <-{ it_layout size_t }
          LocInfoE loc_99 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_99 (i2v 5 i32))) ;
        locinfo: loc_88 ;
        "_" <- LocInfoE loc_94 (global_fork) with
          [ LocInfoE loc_95 (global_test_thread_safe_alloc_fork_fn) ;
          LocInfoE loc_96 (&(LocInfoE loc_97 (global_param))) ] ;
        locinfo: loc_89 ;
        "_" <- LocInfoE loc_91 (global_thread_safe_alloc) with
          [ LocInfoE loc_92 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_92 (i2v 5 i32))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
