From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/paper_example_2_1.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/paper_example_2_1.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 29 2 29 40.
  Definition loc_12 : location_info := LocationInfo file_1 30 2 30 15.
  Definition loc_13 : location_info := LocationInfo file_1 31 2 31 28.
  Definition loc_14 : location_info := LocationInfo file_1 31 9 31 27.
  Definition loc_15 : location_info := LocationInfo file_1 31 9 31 18.
  Definition loc_16 : location_info := LocationInfo file_1 31 9 31 18.
  Definition loc_17 : location_info := LocationInfo file_1 31 9 31 10.
  Definition loc_18 : location_info := LocationInfo file_1 31 9 31 10.
  Definition loc_19 : location_info := LocationInfo file_1 31 21 31 27.
  Definition loc_20 : location_info := LocationInfo file_1 31 21 31 27.
  Definition loc_21 : location_info := LocationInfo file_1 31 21 31 22.
  Definition loc_22 : location_info := LocationInfo file_1 31 21 31 22.
  Definition loc_23 : location_info := LocationInfo file_1 30 2 30 8.
  Definition loc_24 : location_info := LocationInfo file_1 30 2 30 3.
  Definition loc_25 : location_info := LocationInfo file_1 30 2 30 3.
  Definition loc_26 : location_info := LocationInfo file_1 30 2 30 14.
  Definition loc_27 : location_info := LocationInfo file_1 30 2 30 8.
  Definition loc_28 : location_info := LocationInfo file_1 30 2 30 8.
  Definition loc_29 : location_info := LocationInfo file_1 30 2 30 3.
  Definition loc_30 : location_info := LocationInfo file_1 30 2 30 3.
  Definition loc_31 : location_info := LocationInfo file_1 30 12 30 14.
  Definition loc_32 : location_info := LocationInfo file_1 30 12 30 14.
  Definition loc_33 : location_info := LocationInfo file_1 29 18 29 40.
  Definition loc_34 : location_info := LocationInfo file_1 29 25 29 39.
  Definition loc_36 : location_info := LocationInfo file_1 29 5 29 16.
  Definition loc_37 : location_info := LocationInfo file_1 29 5 29 7.
  Definition loc_38 : location_info := LocationInfo file_1 29 5 29 7.
  Definition loc_39 : location_info := LocationInfo file_1 29 10 29 16.
  Definition loc_40 : location_info := LocationInfo file_1 29 10 29 16.
  Definition loc_41 : location_info := LocationInfo file_1 29 10 29 11.
  Definition loc_42 : location_info := LocationInfo file_1 29 10 29 11.
  Definition loc_45 : location_info := LocationInfo file_1 41 2 41 40.
  Definition loc_46 : location_info := LocationInfo file_1 42 2 42 15.
  Definition loc_47 : location_info := LocationInfo file_1 43 2 43 33.
  Definition loc_48 : location_info := LocationInfo file_1 44 2 44 18.
  Definition loc_49 : location_info := LocationInfo file_1 45 2 45 13.
  Definition loc_50 : location_info := LocationInfo file_1 45 9 45 12.
  Definition loc_51 : location_info := LocationInfo file_1 45 9 45 12.
  Definition loc_52 : location_info := LocationInfo file_1 44 2 44 11.
  Definition loc_53 : location_info := LocationInfo file_1 44 2 44 3.
  Definition loc_54 : location_info := LocationInfo file_1 44 2 44 3.
  Definition loc_55 : location_info := LocationInfo file_1 44 2 44 17.
  Definition loc_56 : location_info := LocationInfo file_1 44 2 44 11.
  Definition loc_57 : location_info := LocationInfo file_1 44 2 44 11.
  Definition loc_58 : location_info := LocationInfo file_1 44 2 44 3.
  Definition loc_59 : location_info := LocationInfo file_1 44 2 44 3.
  Definition loc_60 : location_info := LocationInfo file_1 44 15 44 17.
  Definition loc_61 : location_info := LocationInfo file_1 44 15 44 17.
  Definition loc_62 : location_info := LocationInfo file_1 43 23 43 32.
  Definition loc_63 : location_info := LocationInfo file_1 43 23 43 32.
  Definition loc_64 : location_info := LocationInfo file_1 43 23 43 24.
  Definition loc_65 : location_info := LocationInfo file_1 43 23 43 24.
  Definition loc_68 : location_info := LocationInfo file_1 42 2 42 8.
  Definition loc_69 : location_info := LocationInfo file_1 42 2 42 3.
  Definition loc_70 : location_info := LocationInfo file_1 42 2 42 3.
  Definition loc_71 : location_info := LocationInfo file_1 42 2 42 14.
  Definition loc_72 : location_info := LocationInfo file_1 42 2 42 8.
  Definition loc_73 : location_info := LocationInfo file_1 42 2 42 8.
  Definition loc_74 : location_info := LocationInfo file_1 42 2 42 3.
  Definition loc_75 : location_info := LocationInfo file_1 42 2 42 3.
  Definition loc_76 : location_info := LocationInfo file_1 42 12 42 14.
  Definition loc_77 : location_info := LocationInfo file_1 42 12 42 14.
  Definition loc_78 : location_info := LocationInfo file_1 41 18 41 40.
  Definition loc_79 : location_info := LocationInfo file_1 41 25 41 39.
  Definition loc_81 : location_info := LocationInfo file_1 41 5 41 16.
  Definition loc_82 : location_info := LocationInfo file_1 41 5 41 7.
  Definition loc_83 : location_info := LocationInfo file_1 41 5 41 7.
  Definition loc_84 : location_info := LocationInfo file_1 41 10 41 16.
  Definition loc_85 : location_info := LocationInfo file_1 41 10 41 16.
  Definition loc_86 : location_info := LocationInfo file_1 41 10 41 11.
  Definition loc_87 : location_info := LocationInfo file_1 41 10 41 11.
  Definition loc_90 : location_info := LocationInfo file_1 63 2 63 17.
  Definition loc_91 : location_info := LocationInfo file_1 64 2 64 35.
  Definition loc_92 : location_info := LocationInfo file_1 64 35 64 3.
  Definition loc_93 : location_info := LocationInfo file_1 65 2 65 33.
  Definition loc_94 : location_info := LocationInfo file_1 66 2 66 19.
  Definition loc_95 : location_info := LocationInfo file_1 67 2 67 13.
  Definition loc_96 : location_info := LocationInfo file_1 67 9 67 12.
  Definition loc_97 : location_info := LocationInfo file_1 67 9 67 12.
  Definition loc_98 : location_info := LocationInfo file_1 66 2 66 11.
  Definition loc_99 : location_info := LocationInfo file_1 66 2 66 11.
  Definition loc_100 : location_info := LocationInfo file_1 66 12 66 17.
  Definition loc_101 : location_info := LocationInfo file_1 66 13 66 17.
  Definition loc_102 : location_info := LocationInfo file_1 65 14 65 32.
  Definition loc_103 : location_info := LocationInfo file_1 65 14 65 19.
  Definition loc_104 : location_info := LocationInfo file_1 65 14 65 19.
  Definition loc_105 : location_info := LocationInfo file_1 65 20 65 25.
  Definition loc_106 : location_info := LocationInfo file_1 65 21 65 25.
  Definition loc_107 : location_info := LocationInfo file_1 65 27 65 31.
  Definition loc_108 : location_info := LocationInfo file_1 65 27 65 31.
  Definition loc_111 : location_info := LocationInfo file_1 64 27 64 34.
  Definition loc_112 : location_info := LocationInfo file_1 64 28 64 34.
  Definition loc_113 : location_info := LocationInfo file_1 63 2 63 9.
  Definition loc_114 : location_info := LocationInfo file_1 63 2 63 9.
  Definition loc_115 : location_info := LocationInfo file_1 63 10 63 15.
  Definition loc_116 : location_info := LocationInfo file_1 63 11 63 15.
  Definition loc_119 : location_info := LocationInfo file_1 81 2 81 10.
  Definition loc_120 : location_info := LocationInfo file_1 81 2 81 4.
  Definition loc_121 : location_info := LocationInfo file_1 81 2 81 4.
  Definition loc_122 : location_info := LocationInfo file_1 81 2 81 4.
  Definition loc_123 : location_info := LocationInfo file_1 81 5 81 8.
  Definition loc_124 : location_info := LocationInfo file_1 81 5 81 8.
  Definition loc_127 : location_info := LocationInfo file_1 87 2 87 24.
  Definition loc_128 : location_info := LocationInfo file_1 88 2 88 30.
  Definition loc_129 : location_info := LocationInfo file_1 88 2 88 19.
  Definition loc_130 : location_info := LocationInfo file_1 88 2 88 19.
  Definition loc_131 : location_info := LocationInfo file_1 88 20 88 28.
  Definition loc_132 : location_info := LocationInfo file_1 88 20 88 28.
  Definition loc_133 : location_info := LocationInfo file_1 88 21 88 28.
  Definition loc_134 : location_info := LocationInfo file_1 88 21 88 28.
  Definition loc_135 : location_info := LocationInfo file_1 87 20 87 23.
  Definition loc_136 : location_info := LocationInfo file_1 87 20 87 23.
  Definition loc_141 : location_info := LocationInfo file_1 97 2 97 12.
  Definition loc_142 : location_info := LocationInfo file_1 98 2 98 47.
  Definition loc_143 : location_info := LocationInfo file_1 99 2 99 23.
  Definition loc_144 : location_info := LocationInfo file_1 99 2 99 19.
  Definition loc_145 : location_info := LocationInfo file_1 99 2 99 19.
  Definition loc_146 : location_info := LocationInfo file_1 99 20 99 21.
  Definition loc_147 : location_info := LocationInfo file_1 98 2 98 6.
  Definition loc_148 : location_info := LocationInfo file_1 98 2 98 6.
  Definition loc_149 : location_info := LocationInfo file_1 98 7 98 37.
  Definition loc_150 : location_info := LocationInfo file_1 98 39 98 45.
  Definition loc_151 : location_info := LocationInfo file_1 98 40 98 45.
  Definition loc_152 : location_info := LocationInfo file_1 97 2 97 7.
  Definition loc_153 : location_info := LocationInfo file_1 97 10 97 11.

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
        locinfo: loc_36 ;
        if: LocInfoE loc_36 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_36 ((LocInfoE loc_37 (use{IntOp size_t} (LocInfoE loc_38 ("sz")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_39 (use{IntOp size_t} (LocInfoE loc_40 ((LocInfoE loc_41 (!{PtrOp} (LocInfoE loc_42 ("d")))) at{struct_mem_t} "len")))))))
        then
        locinfo: loc_33 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_12 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp size_t} (LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_31 (use{IntOp size_t} (LocInfoE loc_32 ("sz"))))) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 ((LocInfoE loc_15 (use{PtrOp} (LocInfoE loc_16 ((LocInfoE loc_17 (!{PtrOp} (LocInfoE loc_18 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_19 (use{IntOp size_t} (LocInfoE loc_20 ((LocInfoE loc_21 (!{PtrOp} (LocInfoE loc_22 ("d")))) at{struct_mem_t} "len"))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_33 ;
        Return (LocInfoE loc_34 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
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
        locinfo: loc_81 ;
        if: LocInfoE loc_81 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_81 ((LocInfoE loc_82 (use{IntOp size_t} (LocInfoE loc_83 ("sz")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_84 (use{IntOp size_t} (LocInfoE loc_85 ((LocInfoE loc_86 (!{PtrOp} (LocInfoE loc_87 ("d")))) at{struct_mem_t} "len")))))))
        then
        locinfo: loc_78 ;
          Goto "#2"
        else
        locinfo: loc_46 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_46 ;
        LocInfoE loc_68 ((LocInfoE loc_69 (!{PtrOp} (LocInfoE loc_70 ("d")))) at{struct_mem_t} "len") <-{ IntOp size_t }
          LocInfoE loc_71 ((LocInfoE loc_72 (use{IntOp size_t} (LocInfoE loc_73 ((LocInfoE loc_74 (!{PtrOp} (LocInfoE loc_75 ("d")))) at{struct_mem_t} "len")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_76 (use{IntOp size_t} (LocInfoE loc_77 ("sz"))))) ;
        "res" <-{ PtrOp }
          LocInfoE loc_62 (use{PtrOp} (LocInfoE loc_63 ((LocInfoE loc_64 (!{PtrOp} (LocInfoE loc_65 ("d")))) at{struct_mem_t} "buffer"))) ;
        locinfo: loc_48 ;
        LocInfoE loc_52 ((LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("d")))) at{struct_mem_t} "buffer") <-{ PtrOp }
          LocInfoE loc_55 ((LocInfoE loc_56 (use{PtrOp} (LocInfoE loc_57 ((LocInfoE loc_58 (!{PtrOp} (LocInfoE loc_59 ("d")))) at{struct_mem_t} "buffer")))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_60 (use{IntOp size_t} (LocInfoE loc_61 ("sz"))))) ;
        locinfo: loc_49 ;
        Return (LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("res"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_78 ;
        Return (LocInfoE loc_79 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_46 ;
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
        locinfo: loc_90 ;
        expr: (LocInfoE loc_90 (Call (LocInfoE loc_114 (global_sl_lock)) [@{expr} LocInfoE loc_115 (&(LocInfoE loc_116 (global_lock))) ])) ;
        locinfo: loc_91 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_111 (&(LocInfoE loc_112 (global_data)))) ;
        "ret" <-{ PtrOp }
          LocInfoE loc_102 (Call (LocInfoE loc_104 (global_alloc)) [@{expr} LocInfoE loc_105 (&(LocInfoE loc_106 (global_data))) ;
          LocInfoE loc_107 (use{IntOp size_t} (LocInfoE loc_108 ("size"))) ]) ;
        locinfo: loc_94 ;
        expr: (LocInfoE loc_94 (Call (LocInfoE loc_99 (global_sl_unlock)) [@{expr} LocInfoE loc_100 (AnnotExpr 1%nat LockA (LocInfoE loc_100 (&(LocInfoE loc_101 (global_lock))))) ])) ;
        locinfo: loc_95 ;
        Return (LocInfoE loc_96 (use{PtrOp} (LocInfoE loc_97 ("ret"))))
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
        locinfo: loc_119 ;
        expr: (LocInfoE loc_119 (Call (LocInfoE loc_121 (use{PtrOp} (LocInfoE loc_122 ("fn")))) [@{expr} LocInfoE loc_123 (use{PtrOp} (LocInfoE loc_124 ("arg"))) ])) ;
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
        "num_int" <-{ PtrOp }
          LocInfoE loc_135 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_135 (use{PtrOp} (LocInfoE loc_136 ("num"))))) ;
        locinfo: loc_128 ;
        expr: (LocInfoE loc_128 (Call (LocInfoE loc_130 (global_thread_safe_alloc)) [@{expr} LocInfoE loc_131 (use{IntOp size_t} (LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_134 ("num_int"))))) ])) ;
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
        locinfo: loc_141 ;
        LocInfoE loc_152 (global_param) <-{ IntOp size_t }
          LocInfoE loc_153 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_153 (i2v 5 i32))) ;
        locinfo: loc_142 ;
        expr: (LocInfoE loc_142 (Call (LocInfoE loc_148 (global_fork)) [@{expr} LocInfoE loc_149 (global_test_thread_safe_alloc_fork_fn) ;
        LocInfoE loc_150 (&(LocInfoE loc_151 (global_param))) ])) ;
        locinfo: loc_143 ;
        expr: (LocInfoE loc_143 (Call (LocInfoE loc_145 (global_thread_safe_alloc)) [@{expr} LocInfoE loc_146 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_146 (i2v 5 i32))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
