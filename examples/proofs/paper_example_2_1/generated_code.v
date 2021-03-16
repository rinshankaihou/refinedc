From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section code.
  Definition file_0 : string := "examples/paper_example_2_1.c".
  Definition loc_2 : location_info := LocationInfo file_0 29 2 29 40.
  Definition loc_3 : location_info := LocationInfo file_0 30 2 30 15.
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
  Definition loc_17 : location_info := LocationInfo file_0 30 2 30 14.
  Definition loc_18 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_19 : location_info := LocationInfo file_0 30 2 30 8.
  Definition loc_20 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_21 : location_info := LocationInfo file_0 30 2 30 3.
  Definition loc_22 : location_info := LocationInfo file_0 30 12 30 14.
  Definition loc_23 : location_info := LocationInfo file_0 30 12 30 14.
  Definition loc_24 : location_info := LocationInfo file_0 29 18 29 40.
  Definition loc_25 : location_info := LocationInfo file_0 29 25 29 39.
  Definition loc_27 : location_info := LocationInfo file_0 29 5 29 16.
  Definition loc_28 : location_info := LocationInfo file_0 29 5 29 7.
  Definition loc_29 : location_info := LocationInfo file_0 29 5 29 7.
  Definition loc_30 : location_info := LocationInfo file_0 29 10 29 16.
  Definition loc_31 : location_info := LocationInfo file_0 29 10 29 16.
  Definition loc_32 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_33 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_36 : location_info := LocationInfo file_0 41 2 41 40.
  Definition loc_37 : location_info := LocationInfo file_0 42 2 42 15.
  Definition loc_38 : location_info := LocationInfo file_0 43 2 43 33.
  Definition loc_39 : location_info := LocationInfo file_0 44 2 44 18.
  Definition loc_40 : location_info := LocationInfo file_0 45 2 45 13.
  Definition loc_41 : location_info := LocationInfo file_0 45 9 45 12.
  Definition loc_42 : location_info := LocationInfo file_0 45 9 45 12.
  Definition loc_43 : location_info := LocationInfo file_0 44 2 44 11.
  Definition loc_44 : location_info := LocationInfo file_0 44 2 44 3.
  Definition loc_45 : location_info := LocationInfo file_0 44 2 44 3.
  Definition loc_46 : location_info := LocationInfo file_0 44 2 44 17.
  Definition loc_47 : location_info := LocationInfo file_0 44 2 44 11.
  Definition loc_48 : location_info := LocationInfo file_0 44 2 44 11.
  Definition loc_49 : location_info := LocationInfo file_0 44 2 44 3.
  Definition loc_50 : location_info := LocationInfo file_0 44 2 44 3.
  Definition loc_51 : location_info := LocationInfo file_0 44 15 44 17.
  Definition loc_52 : location_info := LocationInfo file_0 44 15 44 17.
  Definition loc_53 : location_info := LocationInfo file_0 43 23 43 32.
  Definition loc_54 : location_info := LocationInfo file_0 43 23 43 32.
  Definition loc_55 : location_info := LocationInfo file_0 43 23 43 24.
  Definition loc_56 : location_info := LocationInfo file_0 43 23 43 24.
  Definition loc_59 : location_info := LocationInfo file_0 42 2 42 8.
  Definition loc_60 : location_info := LocationInfo file_0 42 2 42 3.
  Definition loc_61 : location_info := LocationInfo file_0 42 2 42 3.
  Definition loc_62 : location_info := LocationInfo file_0 42 2 42 14.
  Definition loc_63 : location_info := LocationInfo file_0 42 2 42 8.
  Definition loc_64 : location_info := LocationInfo file_0 42 2 42 8.
  Definition loc_65 : location_info := LocationInfo file_0 42 2 42 3.
  Definition loc_66 : location_info := LocationInfo file_0 42 2 42 3.
  Definition loc_67 : location_info := LocationInfo file_0 42 12 42 14.
  Definition loc_68 : location_info := LocationInfo file_0 42 12 42 14.
  Definition loc_69 : location_info := LocationInfo file_0 41 18 41 40.
  Definition loc_70 : location_info := LocationInfo file_0 41 25 41 39.
  Definition loc_72 : location_info := LocationInfo file_0 41 5 41 16.
  Definition loc_73 : location_info := LocationInfo file_0 41 5 41 7.
  Definition loc_74 : location_info := LocationInfo file_0 41 5 41 7.
  Definition loc_75 : location_info := LocationInfo file_0 41 10 41 16.
  Definition loc_76 : location_info := LocationInfo file_0 41 10 41 16.
  Definition loc_77 : location_info := LocationInfo file_0 41 10 41 11.
  Definition loc_78 : location_info := LocationInfo file_0 41 10 41 11.
  Definition loc_81 : location_info := LocationInfo file_0 63 2 63 17.
  Definition loc_82 : location_info := LocationInfo file_0 64 2 64 35.
  Definition loc_83 : location_info := LocationInfo file_0 64 35 64 3.
  Definition loc_84 : location_info := LocationInfo file_0 65 2 65 33.
  Definition loc_85 : location_info := LocationInfo file_0 66 2 66 19.
  Definition loc_86 : location_info := LocationInfo file_0 67 2 67 13.
  Definition loc_87 : location_info := LocationInfo file_0 67 9 67 12.
  Definition loc_88 : location_info := LocationInfo file_0 67 9 67 12.
  Definition loc_89 : location_info := LocationInfo file_0 66 2 66 11.
  Definition loc_90 : location_info := LocationInfo file_0 66 2 66 11.
  Definition loc_91 : location_info := LocationInfo file_0 66 12 66 17.
  Definition loc_92 : location_info := LocationInfo file_0 66 13 66 17.
  Definition loc_93 : location_info := LocationInfo file_0 65 14 65 32.
  Definition loc_94 : location_info := LocationInfo file_0 65 14 65 19.
  Definition loc_95 : location_info := LocationInfo file_0 65 14 65 19.
  Definition loc_96 : location_info := LocationInfo file_0 65 20 65 25.
  Definition loc_97 : location_info := LocationInfo file_0 65 21 65 25.
  Definition loc_98 : location_info := LocationInfo file_0 65 27 65 31.
  Definition loc_99 : location_info := LocationInfo file_0 65 27 65 31.
  Definition loc_102 : location_info := LocationInfo file_0 64 27 64 34.
  Definition loc_103 : location_info := LocationInfo file_0 64 28 64 34.
  Definition loc_104 : location_info := LocationInfo file_0 63 2 63 9.
  Definition loc_105 : location_info := LocationInfo file_0 63 2 63 9.
  Definition loc_106 : location_info := LocationInfo file_0 63 10 63 15.
  Definition loc_107 : location_info := LocationInfo file_0 63 11 63 15.
  Definition loc_110 : location_info := LocationInfo file_0 81 2 81 10.
  Definition loc_111 : location_info := LocationInfo file_0 81 2 81 4.
  Definition loc_112 : location_info := LocationInfo file_0 81 2 81 4.
  Definition loc_113 : location_info := LocationInfo file_0 81 2 81 4.
  Definition loc_114 : location_info := LocationInfo file_0 81 5 81 8.
  Definition loc_115 : location_info := LocationInfo file_0 81 5 81 8.
  Definition loc_118 : location_info := LocationInfo file_0 87 2 87 24.
  Definition loc_119 : location_info := LocationInfo file_0 88 2 88 30.
  Definition loc_120 : location_info := LocationInfo file_0 88 2 88 19.
  Definition loc_121 : location_info := LocationInfo file_0 88 2 88 19.
  Definition loc_122 : location_info := LocationInfo file_0 88 20 88 28.
  Definition loc_123 : location_info := LocationInfo file_0 88 20 88 28.
  Definition loc_124 : location_info := LocationInfo file_0 88 21 88 28.
  Definition loc_125 : location_info := LocationInfo file_0 88 21 88 28.
  Definition loc_126 : location_info := LocationInfo file_0 87 20 87 23.
  Definition loc_127 : location_info := LocationInfo file_0 87 20 87 23.
  Definition loc_132 : location_info := LocationInfo file_0 97 2 97 12.
  Definition loc_133 : location_info := LocationInfo file_0 98 2 98 47.
  Definition loc_134 : location_info := LocationInfo file_0 99 2 99 23.
  Definition loc_135 : location_info := LocationInfo file_0 99 2 99 19.
  Definition loc_136 : location_info := LocationInfo file_0 99 2 99 19.
  Definition loc_137 : location_info := LocationInfo file_0 99 20 99 21.
  Definition loc_138 : location_info := LocationInfo file_0 98 2 98 6.
  Definition loc_139 : location_info := LocationInfo file_0 98 2 98 6.
  Definition loc_140 : location_info := LocationInfo file_0 98 7 98 37.
  Definition loc_141 : location_info := LocationInfo file_0 98 39 98 45.
  Definition loc_142 : location_info := LocationInfo file_0 98 40 98 45.
  Definition loc_143 : location_info := LocationInfo file_0 97 2 97 7.
  Definition loc_144 : location_info := LocationInfo file_0 97 10 97 11.

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
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        if: LocInfoE loc_27 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_27 ((LocInfoE loc_28 (use{it_layout size_t} (LocInfoE loc_29 ("sz")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_30 (use{it_layout size_t} (LocInfoE loc_31 ((LocInfoE loc_32 (!{void*} (LocInfoE loc_33 ("d")))) at{struct_mem_t} "len")))))))
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
          LocInfoE loc_17 ((LocInfoE loc_18 (use{it_layout size_t} (LocInfoE loc_19 ((LocInfoE loc_20 (!{void*} (LocInfoE loc_21 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_22 (use{it_layout size_t} (LocInfoE loc_23 ("sz"))))) ;
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

  (* Definition of function [alloc_from_start]. *)
  Definition impl_alloc_from_start : function := {|
    f_args := [
      ("d", void*);
      ("sz", it_layout size_t)
    ];
    f_local_vars := [
      ("res", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_72 ;
        if: LocInfoE loc_72 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_72 ((LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ("sz")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_75 (use{it_layout size_t} (LocInfoE loc_76 ((LocInfoE loc_77 (!{void*} (LocInfoE loc_78 ("d")))) at{struct_mem_t} "len")))))))
        then
        locinfo: loc_69 ;
          Goto "#2"
        else
        locinfo: loc_37 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_37 ;
        LocInfoE loc_59 ((LocInfoE loc_60 (!{void*} (LocInfoE loc_61 ("d")))) at{struct_mem_t} "len") <-{ it_layout size_t }
          LocInfoE loc_62 ((LocInfoE loc_63 (use{it_layout size_t} (LocInfoE loc_64 ((LocInfoE loc_65 (!{void*} (LocInfoE loc_66 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_67 (use{it_layout size_t} (LocInfoE loc_68 ("sz"))))) ;
        "res" <-{ void* }
          LocInfoE loc_53 (use{void*} (LocInfoE loc_54 ((LocInfoE loc_55 (!{void*} (LocInfoE loc_56 ("d")))) at{struct_mem_t} "buffer"))) ;
        locinfo: loc_39 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (!{void*} (LocInfoE loc_45 ("d")))) at{struct_mem_t} "buffer") <-{ void* }
          LocInfoE loc_46 ((LocInfoE loc_47 (use{void*} (LocInfoE loc_48 ((LocInfoE loc_49 (!{void*} (LocInfoE loc_50 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_51 (use{it_layout size_t} (LocInfoE loc_52 ("sz"))))) ;
        locinfo: loc_40 ;
        Return (LocInfoE loc_41 (use{void*} (LocInfoE loc_42 ("res"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_69 ;
        Return (LocInfoE loc_70 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_37 ;
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
        locinfo: loc_81 ;
        expr: (LocInfoE loc_81 (Call (LocInfoE loc_105 (global_sl_lock)) [@{expr} LocInfoE loc_106 (&(LocInfoE loc_107 (global_lock))) ])) ;
        locinfo: loc_82 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_102 (&(LocInfoE loc_103 (global_data)))) ;
        "ret" <-{ void* }
          LocInfoE loc_93 (Call (LocInfoE loc_95 (global_alloc)) [@{expr} LocInfoE loc_96 (&(LocInfoE loc_97 (global_data))) ;
          LocInfoE loc_98 (use{it_layout size_t} (LocInfoE loc_99 ("size"))) ]) ;
        locinfo: loc_85 ;
        expr: (LocInfoE loc_85 (Call (LocInfoE loc_90 (global_sl_unlock)) [@{expr} LocInfoE loc_91 (AnnotExpr 1%nat LockA (LocInfoE loc_91 (&(LocInfoE loc_92 (global_lock))))) ])) ;
        locinfo: loc_86 ;
        Return (LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ("ret"))))
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
        locinfo: loc_110 ;
        expr: (LocInfoE loc_110 (Call (LocInfoE loc_112 (use{void*} (LocInfoE loc_113 ("fn")))) [@{expr} LocInfoE loc_114 (use{void*} (LocInfoE loc_115 ("arg"))) ])) ;
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
          LocInfoE loc_126 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_126 (use{void*} (LocInfoE loc_127 ("num"))))) ;
        locinfo: loc_119 ;
        expr: (LocInfoE loc_119 (Call (LocInfoE loc_121 (global_thread_safe_alloc)) [@{expr} LocInfoE loc_122 (use{it_layout size_t} (LocInfoE loc_124 (!{void*} (LocInfoE loc_125 ("num_int"))))) ])) ;
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
        locinfo: loc_132 ;
        LocInfoE loc_143 (global_param) <-{ it_layout size_t }
          LocInfoE loc_144 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_144 (i2v 5 i32))) ;
        locinfo: loc_133 ;
        expr: (LocInfoE loc_133 (Call (LocInfoE loc_139 (global_fork)) [@{expr} LocInfoE loc_140 (global_test_thread_safe_alloc_fork_fn) ;
        LocInfoE loc_141 (&(LocInfoE loc_142 (global_param))) ])) ;
        locinfo: loc_134 ;
        expr: (LocInfoE loc_134 (Call (LocInfoE loc_136 (global_thread_safe_alloc)) [@{expr} LocInfoE loc_137 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_137 (i2v 5 i32))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
