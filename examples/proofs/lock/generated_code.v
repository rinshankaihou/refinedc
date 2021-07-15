From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/lock.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/lock.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 33 4 33 19.
  Definition loc_12 : location_info := LocationInfo file_1 34 4 34 22.
  Definition loc_13 : location_info := LocationInfo file_1 35 4 35 27.
  Definition loc_14 : location_info := LocationInfo file_1 36 4 36 28.
  Definition loc_15 : location_info := LocationInfo file_1 37 4 37 22.
  Definition loc_16 : location_info := LocationInfo file_1 37 4 37 11.
  Definition loc_17 : location_info := LocationInfo file_1 37 4 37 11.
  Definition loc_18 : location_info := LocationInfo file_1 37 12 37 20.
  Definition loc_19 : location_info := LocationInfo file_1 37 13 37 20.
  Definition loc_20 : location_info := LocationInfo file_1 37 13 37 14.
  Definition loc_21 : location_info := LocationInfo file_1 37 13 37 14.
  Definition loc_22 : location_info := LocationInfo file_1 36 4 36 22.
  Definition loc_23 : location_info := LocationInfo file_1 36 4 36 20.
  Definition loc_24 : location_info := LocationInfo file_1 36 4 36 5.
  Definition loc_25 : location_info := LocationInfo file_1 36 4 36 5.
  Definition loc_26 : location_info := LocationInfo file_1 36 25 36 27.
  Definition loc_27 : location_info := LocationInfo file_1 35 4 35 22.
  Definition loc_28 : location_info := LocationInfo file_1 35 4 35 20.
  Definition loc_29 : location_info := LocationInfo file_1 35 4 35 5.
  Definition loc_30 : location_info := LocationInfo file_1 35 4 35 5.
  Definition loc_31 : location_info := LocationInfo file_1 35 25 35 26.
  Definition loc_32 : location_info := LocationInfo file_1 34 4 34 17.
  Definition loc_33 : location_info := LocationInfo file_1 34 4 34 5.
  Definition loc_34 : location_info := LocationInfo file_1 34 4 34 5.
  Definition loc_35 : location_info := LocationInfo file_1 34 20 34 21.
  Definition loc_36 : location_info := LocationInfo file_1 33 4 33 14.
  Definition loc_37 : location_info := LocationInfo file_1 33 4 33 5.
  Definition loc_38 : location_info := LocationInfo file_1 33 4 33 5.
  Definition loc_39 : location_info := LocationInfo file_1 33 17 33 18.
  Definition loc_42 : location_info := LocationInfo file_1 44 4 44 19.
  Definition loc_43 : location_info := LocationInfo file_1 44 4 44 14.
  Definition loc_44 : location_info := LocationInfo file_1 44 4 44 5.
  Definition loc_45 : location_info := LocationInfo file_1 44 4 44 5.
  Definition loc_46 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_47 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_50 : location_info := LocationInfo file_1 52 4 52 22.
  Definition loc_51 : location_info := LocationInfo file_1 52 11 52 21.
  Definition loc_52 : location_info := LocationInfo file_1 52 11 52 21.
  Definition loc_53 : location_info := LocationInfo file_1 52 11 52 12.
  Definition loc_54 : location_info := LocationInfo file_1 52 11 52 12.
  Definition loc_57 : location_info := LocationInfo file_1 59 4 59 22.
  Definition loc_58 : location_info := LocationInfo file_1 61 4 61 46.
  Definition loc_59 : location_info := LocationInfo file_1 61 46 61 5.
  Definition loc_60 : location_info := LocationInfo file_1 63 4 63 22.
  Definition loc_61 : location_info := LocationInfo file_1 64 4 64 24.
  Definition loc_62 : location_info := LocationInfo file_1 64 4 64 13.
  Definition loc_63 : location_info := LocationInfo file_1 64 4 64 13.
  Definition loc_64 : location_info := LocationInfo file_1 64 14 64 22.
  Definition loc_65 : location_info := LocationInfo file_1 64 15 64 22.
  Definition loc_66 : location_info := LocationInfo file_1 64 15 64 16.
  Definition loc_67 : location_info := LocationInfo file_1 64 15 64 16.
  Definition loc_68 : location_info := LocationInfo file_1 63 4 63 17.
  Definition loc_69 : location_info := LocationInfo file_1 63 4 63 5.
  Definition loc_70 : location_info := LocationInfo file_1 63 4 63 5.
  Definition loc_71 : location_info := LocationInfo file_1 63 20 63 21.
  Definition loc_72 : location_info := LocationInfo file_1 63 20 63 21.
  Definition loc_73 : location_info := LocationInfo file_1 61 29 61 45.
  Definition loc_74 : location_info := LocationInfo file_1 61 30 61 45.
  Definition loc_75 : location_info := LocationInfo file_1 61 31 61 32.
  Definition loc_76 : location_info := LocationInfo file_1 61 31 61 32.
  Definition loc_77 : location_info := LocationInfo file_1 59 4 59 11.
  Definition loc_78 : location_info := LocationInfo file_1 59 4 59 11.
  Definition loc_79 : location_info := LocationInfo file_1 59 12 59 20.
  Definition loc_80 : location_info := LocationInfo file_1 59 13 59 20.
  Definition loc_81 : location_info := LocationInfo file_1 59 13 59 14.
  Definition loc_82 : location_info := LocationInfo file_1 59 13 59 14.
  Definition loc_85 : location_info := LocationInfo file_1 73 4 73 22.
  Definition loc_86 : location_info := LocationInfo file_1 74 4 74 46.
  Definition loc_87 : location_info := LocationInfo file_1 74 46 74 5.
  Definition loc_88 : location_info := LocationInfo file_1 76 4 76 31.
  Definition loc_89 : location_info := LocationInfo file_1 78 4 78 24.
  Definition loc_90 : location_info := LocationInfo file_1 79 4 79 15.
  Definition loc_91 : location_info := LocationInfo file_1 79 11 79 14.
  Definition loc_92 : location_info := LocationInfo file_1 79 11 79 14.
  Definition loc_93 : location_info := LocationInfo file_1 78 4 78 13.
  Definition loc_94 : location_info := LocationInfo file_1 78 4 78 13.
  Definition loc_95 : location_info := LocationInfo file_1 78 14 78 22.
  Definition loc_96 : location_info := LocationInfo file_1 78 15 78 22.
  Definition loc_97 : location_info := LocationInfo file_1 78 15 78 16.
  Definition loc_98 : location_info := LocationInfo file_1 78 15 78 16.
  Definition loc_99 : location_info := LocationInfo file_1 76 17 76 30.
  Definition loc_100 : location_info := LocationInfo file_1 76 17 76 30.
  Definition loc_101 : location_info := LocationInfo file_1 76 17 76 18.
  Definition loc_102 : location_info := LocationInfo file_1 76 17 76 18.
  Definition loc_105 : location_info := LocationInfo file_1 74 29 74 45.
  Definition loc_106 : location_info := LocationInfo file_1 74 30 74 45.
  Definition loc_107 : location_info := LocationInfo file_1 74 31 74 32.
  Definition loc_108 : location_info := LocationInfo file_1 74 31 74 32.
  Definition loc_109 : location_info := LocationInfo file_1 73 4 73 11.
  Definition loc_110 : location_info := LocationInfo file_1 73 4 73 11.
  Definition loc_111 : location_info := LocationInfo file_1 73 12 73 20.
  Definition loc_112 : location_info := LocationInfo file_1 73 13 73 20.
  Definition loc_113 : location_info := LocationInfo file_1 73 13 73 14.
  Definition loc_114 : location_info := LocationInfo file_1 73 13 73 14.
  Definition loc_117 : location_info := LocationInfo file_1 88 4 88 22.
  Definition loc_118 : location_info := LocationInfo file_1 89 4 89 49.
  Definition loc_119 : location_info := LocationInfo file_1 89 49 89 5.
  Definition loc_120 : location_info := LocationInfo file_1 91 4 94 5.
  Definition loc_121 : location_info := LocationInfo file_1 95 4 95 36.
  Definition loc_122 : location_info := LocationInfo file_1 97 4 97 24.
  Definition loc_123 : location_info := LocationInfo file_1 98 4 98 15.
  Definition loc_124 : location_info := LocationInfo file_1 98 11 98 14.
  Definition loc_125 : location_info := LocationInfo file_1 98 11 98 14.
  Definition loc_126 : location_info := LocationInfo file_1 97 4 97 13.
  Definition loc_127 : location_info := LocationInfo file_1 97 4 97 13.
  Definition loc_128 : location_info := LocationInfo file_1 97 14 97 22.
  Definition loc_129 : location_info := LocationInfo file_1 97 15 97 22.
  Definition loc_130 : location_info := LocationInfo file_1 97 15 97 16.
  Definition loc_131 : location_info := LocationInfo file_1 97 15 97 16.
  Definition loc_132 : location_info := LocationInfo file_1 95 17 95 35.
  Definition loc_133 : location_info := LocationInfo file_1 95 17 95 35.
  Definition loc_134 : location_info := LocationInfo file_1 95 17 95 33.
  Definition loc_135 : location_info := LocationInfo file_1 95 17 95 18.
  Definition loc_136 : location_info := LocationInfo file_1 95 17 95 18.
  Definition loc_139 : location_info := LocationInfo file_1 91 40 94 5.
  Definition loc_140 : location_info := LocationInfo file_1 92 8 92 32.
  Definition loc_141 : location_info := LocationInfo file_1 93 8 93 32.
  Definition loc_142 : location_info := LocationInfo file_1 93 8 93 26.
  Definition loc_143 : location_info := LocationInfo file_1 93 8 93 24.
  Definition loc_144 : location_info := LocationInfo file_1 93 8 93 9.
  Definition loc_145 : location_info := LocationInfo file_1 93 8 93 9.
  Definition loc_146 : location_info := LocationInfo file_1 93 8 93 31.
  Definition loc_147 : location_info := LocationInfo file_1 93 8 93 26.
  Definition loc_148 : location_info := LocationInfo file_1 93 8 93 26.
  Definition loc_149 : location_info := LocationInfo file_1 93 8 93 24.
  Definition loc_150 : location_info := LocationInfo file_1 93 8 93 9.
  Definition loc_151 : location_info := LocationInfo file_1 93 8 93 9.
  Definition loc_152 : location_info := LocationInfo file_1 93 30 93 31.
  Definition loc_153 : location_info := LocationInfo file_1 92 8 92 26.
  Definition loc_154 : location_info := LocationInfo file_1 92 8 92 24.
  Definition loc_155 : location_info := LocationInfo file_1 92 8 92 9.
  Definition loc_156 : location_info := LocationInfo file_1 92 8 92 9.
  Definition loc_157 : location_info := LocationInfo file_1 92 8 92 31.
  Definition loc_158 : location_info := LocationInfo file_1 92 8 92 26.
  Definition loc_159 : location_info := LocationInfo file_1 92 8 92 26.
  Definition loc_160 : location_info := LocationInfo file_1 92 8 92 24.
  Definition loc_161 : location_info := LocationInfo file_1 92 8 92 9.
  Definition loc_162 : location_info := LocationInfo file_1 92 8 92 9.
  Definition loc_163 : location_info := LocationInfo file_1 92 30 92 31.
  Definition loc_165 : location_info := LocationInfo file_1 91 8 91 38.
  Definition loc_166 : location_info := LocationInfo file_1 91 8 91 26.
  Definition loc_167 : location_info := LocationInfo file_1 91 8 91 26.
  Definition loc_168 : location_info := LocationInfo file_1 91 8 91 24.
  Definition loc_169 : location_info := LocationInfo file_1 91 8 91 9.
  Definition loc_170 : location_info := LocationInfo file_1 91 8 91 9.
  Definition loc_171 : location_info := LocationInfo file_1 91 29 91 38.
  Definition loc_172 : location_info := LocationInfo file_1 91 37 91 38.
  Definition loc_173 : location_info := LocationInfo file_1 89 29 89 48.
  Definition loc_174 : location_info := LocationInfo file_1 89 30 89 48.
  Definition loc_175 : location_info := LocationInfo file_1 89 31 89 32.
  Definition loc_176 : location_info := LocationInfo file_1 89 31 89 32.
  Definition loc_177 : location_info := LocationInfo file_1 88 4 88 11.
  Definition loc_178 : location_info := LocationInfo file_1 88 4 88 11.
  Definition loc_179 : location_info := LocationInfo file_1 88 12 88 20.
  Definition loc_180 : location_info := LocationInfo file_1 88 13 88 20.
  Definition loc_181 : location_info := LocationInfo file_1 88 13 88 14.
  Definition loc_182 : location_info := LocationInfo file_1 88 13 88 14.

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

  (* Definition of struct [lock_test_inner]. *)
  Program Definition struct_lock_test_inner := {|
    sl_members := [
      (Some "a", it_layout size_t);
      (Some "b", it_layout size_t)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [lock_test]. *)
  Program Definition struct_lock_test := {|
    sl_members := [
      (Some "outside", it_layout size_t);
      (Some "lock", layout_of struct_spinlock);
      (None, Layout 7%nat 0%nat);
      (Some "locked_int", it_layout size_t);
      (Some "locked_struct", layout_of struct_lock_test_inner)
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

  (* Definition of function [init]. *)
  Definition impl_init (global_sl_init : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        LocInfoE loc_36 ((LocInfoE loc_37 (!{PtrOp} (LocInfoE loc_38 ("t")))) at{struct_lock_test} "outside") <-{ IntOp size_t }
          LocInfoE loc_39 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_39 (i2v 0 i32))) ;
        locinfo: loc_12 ;
        LocInfoE loc_32 ((LocInfoE loc_33 (!{PtrOp} (LocInfoE loc_34 ("t")))) at{struct_lock_test} "locked_int") <-{ IntOp size_t }
          LocInfoE loc_35 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_35 (i2v 0 i32))) ;
        locinfo: loc_13 ;
        LocInfoE loc_27 ((LocInfoE loc_28 ((LocInfoE loc_29 (!{PtrOp} (LocInfoE loc_30 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a") <-{ IntOp size_t }
          LocInfoE loc_31 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_31 (i2v 0 i32))) ;
        locinfo: loc_14 ;
        LocInfoE loc_22 ((LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b") <-{ IntOp size_t }
          LocInfoE loc_26 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_26 (i2v 10 i32))) ;
        locinfo: loc_15 ;
        expr: (LocInfoE loc_15 (Call (LocInfoE loc_17 (global_sl_init)) [@{expr} LocInfoE loc_18 (&(LocInfoE loc_19 ((LocInfoE loc_20 (!{PtrOp} (LocInfoE loc_21 ("t")))) at{struct_lock_test} "lock"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [write_outside]. *)
  Definition impl_write_outside : function := {|
    f_args := [
      ("t", void*);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_42 ;
        LocInfoE loc_43 ((LocInfoE loc_44 (!{PtrOp} (LocInfoE loc_45 ("t")))) at{struct_lock_test} "outside") <-{ IntOp size_t }
          LocInfoE loc_46 (use{IntOp size_t} (LocInfoE loc_47 ("n"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [read_outside]. *)
  Definition impl_read_outside : function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_50 ;
        Return (LocInfoE loc_51 (use{IntOp size_t} (LocInfoE loc_52 ((LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("t")))) at{struct_lock_test} "outside"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [write_locked]. *)
  Definition impl_write_locked (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("t", void*);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_57 ;
        expr: (LocInfoE loc_57 (Call (LocInfoE loc_78 (global_sl_lock)) [@{expr} LocInfoE loc_79 (&(LocInfoE loc_80 ((LocInfoE loc_81 (!{PtrOp} (LocInfoE loc_82 ("t")))) at{struct_lock_test} "lock"))) ])) ;
        locinfo: loc_58 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_73 (&(LocInfoE loc_74 ((LocInfoE loc_75 (!{PtrOp} (LocInfoE loc_76 ("t")))) at{struct_lock_test} "locked_int")))) ;
        locinfo: loc_60 ;
        LocInfoE loc_68 ((LocInfoE loc_69 (!{PtrOp} (LocInfoE loc_70 ("t")))) at{struct_lock_test} "locked_int") <-{ IntOp size_t }
          LocInfoE loc_71 (use{IntOp size_t} (LocInfoE loc_72 ("n"))) ;
        locinfo: loc_61 ;
        expr: (LocInfoE loc_61 (Call (LocInfoE loc_63 (global_sl_unlock)) [@{expr} LocInfoE loc_64 (AnnotExpr 1%nat LockA (LocInfoE loc_64 (&(LocInfoE loc_65 ((LocInfoE loc_66 (!{PtrOp} (LocInfoE loc_67 ("t")))) at{struct_lock_test} "lock"))))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [read_locked]. *)
  Definition impl_read_locked (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
      ("ret", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_85 ;
        expr: (LocInfoE loc_85 (Call (LocInfoE loc_110 (global_sl_lock)) [@{expr} LocInfoE loc_111 (&(LocInfoE loc_112 ((LocInfoE loc_113 (!{PtrOp} (LocInfoE loc_114 ("t")))) at{struct_lock_test} "lock"))) ])) ;
        locinfo: loc_86 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_105 (&(LocInfoE loc_106 ((LocInfoE loc_107 (!{PtrOp} (LocInfoE loc_108 ("t")))) at{struct_lock_test} "locked_int")))) ;
        "ret" <-{ IntOp size_t }
          LocInfoE loc_99 (use{IntOp size_t} (LocInfoE loc_100 ((LocInfoE loc_101 (!{PtrOp} (LocInfoE loc_102 ("t")))) at{struct_lock_test} "locked_int"))) ;
        locinfo: loc_89 ;
        expr: (LocInfoE loc_89 (Call (LocInfoE loc_94 (global_sl_unlock)) [@{expr} LocInfoE loc_95 (AnnotExpr 1%nat LockA (LocInfoE loc_95 (&(LocInfoE loc_96 ((LocInfoE loc_97 (!{PtrOp} (LocInfoE loc_98 ("t")))) at{struct_lock_test} "lock"))))) ])) ;
        locinfo: loc_90 ;
        Return (LocInfoE loc_91 (use{IntOp size_t} (LocInfoE loc_92 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [increment]. *)
  Definition impl_increment (global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("t", void*)
    ];
    f_local_vars := [
      ("ret", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_117 ;
        expr: (LocInfoE loc_117 (Call (LocInfoE loc_178 (global_sl_lock)) [@{expr} LocInfoE loc_179 (&(LocInfoE loc_180 ((LocInfoE loc_181 (!{PtrOp} (LocInfoE loc_182 ("t")))) at{struct_lock_test} "lock"))) ])) ;
        locinfo: loc_118 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_173 (&(LocInfoE loc_174 ((LocInfoE loc_175 (!{PtrOp} (LocInfoE loc_176 ("t")))) at{struct_lock_test} "locked_struct")))) ;
        locinfo: loc_165 ;
        if: LocInfoE loc_165 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_165 ((LocInfoE loc_166 (use{IntOp size_t} (LocInfoE loc_167 ((LocInfoE loc_168 ((LocInfoE loc_169 (!{PtrOp} (LocInfoE loc_170 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_171 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_172 (i2v 0 i32)))))))
        then
        locinfo: loc_140 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ IntOp size_t }
          LocInfoE loc_132 (use{IntOp size_t} (LocInfoE loc_133 ((LocInfoE loc_134 ((LocInfoE loc_135 (!{PtrOp} (LocInfoE loc_136 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a"))) ;
        locinfo: loc_122 ;
        expr: (LocInfoE loc_122 (Call (LocInfoE loc_127 (global_sl_unlock)) [@{expr} LocInfoE loc_128 (AnnotExpr 1%nat LockA (LocInfoE loc_128 (&(LocInfoE loc_129 ((LocInfoE loc_130 (!{PtrOp} (LocInfoE loc_131 ("t")))) at{struct_lock_test} "lock"))))) ])) ;
        locinfo: loc_123 ;
        Return (LocInfoE loc_124 (use{IntOp size_t} (LocInfoE loc_125 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_140 ;
        LocInfoE loc_153 ((LocInfoE loc_154 ((LocInfoE loc_155 (!{PtrOp} (LocInfoE loc_156 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a") <-{ IntOp size_t }
          LocInfoE loc_157 ((LocInfoE loc_158 (use{IntOp size_t} (LocInfoE loc_159 ((LocInfoE loc_160 ((LocInfoE loc_161 (!{PtrOp} (LocInfoE loc_162 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_163 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_163 (i2v 1 i32))))) ;
        locinfo: loc_141 ;
        LocInfoE loc_142 ((LocInfoE loc_143 ((LocInfoE loc_144 (!{PtrOp} (LocInfoE loc_145 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b") <-{ IntOp size_t }
          LocInfoE loc_146 ((LocInfoE loc_147 (use{IntOp size_t} (LocInfoE loc_148 ((LocInfoE loc_149 ((LocInfoE loc_150 (!{PtrOp} (LocInfoE loc_151 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_152 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_152 (i2v 1 i32))))) ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
