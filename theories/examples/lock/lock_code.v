From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [theories/examples/lock/lock.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/lock/lock.c".
  Definition loc_2 : location_info := LocationInfo file_0 34 4 34 19.
  Definition loc_3 : location_info := LocationInfo file_0 35 4 35 22.
  Definition loc_4 : location_info := LocationInfo file_0 36 4 36 27.
  Definition loc_5 : location_info := LocationInfo file_0 37 4 37 28.
  Definition loc_6 : location_info := LocationInfo file_0 38 4 38 22.
  Definition loc_7 : location_info := LocationInfo file_0 38 4 38 11.
  Definition loc_8 : location_info := LocationInfo file_0 38 4 38 11.
  Definition loc_9 : location_info := LocationInfo file_0 38 12 38 20.
  Definition loc_10 : location_info := LocationInfo file_0 38 13 38 20.
  Definition loc_11 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_12 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_13 : location_info := LocationInfo file_0 37 4 37 22.
  Definition loc_14 : location_info := LocationInfo file_0 37 4 37 20.
  Definition loc_15 : location_info := LocationInfo file_0 37 4 37 5.
  Definition loc_16 : location_info := LocationInfo file_0 37 4 37 5.
  Definition loc_17 : location_info := LocationInfo file_0 37 25 37 27.
  Definition loc_18 : location_info := LocationInfo file_0 36 4 36 22.
  Definition loc_19 : location_info := LocationInfo file_0 36 4 36 20.
  Definition loc_20 : location_info := LocationInfo file_0 36 4 36 5.
  Definition loc_21 : location_info := LocationInfo file_0 36 4 36 5.
  Definition loc_22 : location_info := LocationInfo file_0 36 25 36 26.
  Definition loc_23 : location_info := LocationInfo file_0 35 4 35 17.
  Definition loc_24 : location_info := LocationInfo file_0 35 4 35 5.
  Definition loc_25 : location_info := LocationInfo file_0 35 4 35 5.
  Definition loc_26 : location_info := LocationInfo file_0 35 20 35 21.
  Definition loc_27 : location_info := LocationInfo file_0 34 4 34 14.
  Definition loc_28 : location_info := LocationInfo file_0 34 4 34 5.
  Definition loc_29 : location_info := LocationInfo file_0 34 4 34 5.
  Definition loc_30 : location_info := LocationInfo file_0 34 17 34 18.
  Definition loc_33 : location_info := LocationInfo file_0 45 4 45 19.
  Definition loc_34 : location_info := LocationInfo file_0 45 4 45 14.
  Definition loc_35 : location_info := LocationInfo file_0 45 4 45 5.
  Definition loc_36 : location_info := LocationInfo file_0 45 4 45 5.
  Definition loc_37 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_38 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_41 : location_info := LocationInfo file_0 53 4 53 22.
  Definition loc_42 : location_info := LocationInfo file_0 53 11 53 21.
  Definition loc_43 : location_info := LocationInfo file_0 53 11 53 21.
  Definition loc_44 : location_info := LocationInfo file_0 53 11 53 12.
  Definition loc_45 : location_info := LocationInfo file_0 53 11 53 12.
  Definition loc_48 : location_info := LocationInfo file_0 60 4 60 22.
  Definition loc_49 : location_info := LocationInfo file_0 62 4 62 46.
  Definition loc_50 : location_info := LocationInfo file_0 62 46 62 5.
  Definition loc_51 : location_info := LocationInfo file_0 64 4 64 22.
  Definition loc_52 : location_info := LocationInfo file_0 65 4 65 24.
  Definition loc_53 : location_info := LocationInfo file_0 65 4 65 13.
  Definition loc_54 : location_info := LocationInfo file_0 65 4 65 13.
  Definition loc_55 : location_info := LocationInfo file_0 65 14 65 22.
  Definition loc_56 : location_info := LocationInfo file_0 65 15 65 22.
  Definition loc_57 : location_info := LocationInfo file_0 65 15 65 16.
  Definition loc_58 : location_info := LocationInfo file_0 65 15 65 16.
  Definition loc_59 : location_info := LocationInfo file_0 64 4 64 17.
  Definition loc_60 : location_info := LocationInfo file_0 64 4 64 5.
  Definition loc_61 : location_info := LocationInfo file_0 64 4 64 5.
  Definition loc_62 : location_info := LocationInfo file_0 64 20 64 21.
  Definition loc_63 : location_info := LocationInfo file_0 64 20 64 21.
  Definition loc_64 : location_info := LocationInfo file_0 62 29 62 45.
  Definition loc_65 : location_info := LocationInfo file_0 62 30 62 45.
  Definition loc_66 : location_info := LocationInfo file_0 62 31 62 32.
  Definition loc_67 : location_info := LocationInfo file_0 62 31 62 32.
  Definition loc_68 : location_info := LocationInfo file_0 60 4 60 11.
  Definition loc_69 : location_info := LocationInfo file_0 60 4 60 11.
  Definition loc_70 : location_info := LocationInfo file_0 60 12 60 20.
  Definition loc_71 : location_info := LocationInfo file_0 60 13 60 20.
  Definition loc_72 : location_info := LocationInfo file_0 60 13 60 14.
  Definition loc_73 : location_info := LocationInfo file_0 60 13 60 14.
  Definition loc_76 : location_info := LocationInfo file_0 74 4 74 22.
  Definition loc_77 : location_info := LocationInfo file_0 75 4 75 46.
  Definition loc_78 : location_info := LocationInfo file_0 75 46 75 5.
  Definition loc_79 : location_info := LocationInfo file_0 77 4 77 31.
  Definition loc_80 : location_info := LocationInfo file_0 79 4 79 24.
  Definition loc_81 : location_info := LocationInfo file_0 80 4 80 15.
  Definition loc_82 : location_info := LocationInfo file_0 80 11 80 14.
  Definition loc_83 : location_info := LocationInfo file_0 80 11 80 14.
  Definition loc_84 : location_info := LocationInfo file_0 79 4 79 13.
  Definition loc_85 : location_info := LocationInfo file_0 79 4 79 13.
  Definition loc_86 : location_info := LocationInfo file_0 79 14 79 22.
  Definition loc_87 : location_info := LocationInfo file_0 79 15 79 22.
  Definition loc_88 : location_info := LocationInfo file_0 79 15 79 16.
  Definition loc_89 : location_info := LocationInfo file_0 79 15 79 16.
  Definition loc_90 : location_info := LocationInfo file_0 77 17 77 30.
  Definition loc_91 : location_info := LocationInfo file_0 77 17 77 30.
  Definition loc_92 : location_info := LocationInfo file_0 77 17 77 18.
  Definition loc_93 : location_info := LocationInfo file_0 77 17 77 18.
  Definition loc_96 : location_info := LocationInfo file_0 75 29 75 45.
  Definition loc_97 : location_info := LocationInfo file_0 75 30 75 45.
  Definition loc_98 : location_info := LocationInfo file_0 75 31 75 32.
  Definition loc_99 : location_info := LocationInfo file_0 75 31 75 32.
  Definition loc_100 : location_info := LocationInfo file_0 74 4 74 11.
  Definition loc_101 : location_info := LocationInfo file_0 74 4 74 11.
  Definition loc_102 : location_info := LocationInfo file_0 74 12 74 20.
  Definition loc_103 : location_info := LocationInfo file_0 74 13 74 20.
  Definition loc_104 : location_info := LocationInfo file_0 74 13 74 14.
  Definition loc_105 : location_info := LocationInfo file_0 74 13 74 14.
  Definition loc_108 : location_info := LocationInfo file_0 89 4 89 22.
  Definition loc_109 : location_info := LocationInfo file_0 90 4 90 49.
  Definition loc_110 : location_info := LocationInfo file_0 90 49 90 5.
  Definition loc_111 : location_info := LocationInfo file_0 92 4 95 5.
  Definition loc_112 : location_info := LocationInfo file_0 96 4 96 36.
  Definition loc_113 : location_info := LocationInfo file_0 98 4 98 24.
  Definition loc_114 : location_info := LocationInfo file_0 99 4 99 15.
  Definition loc_115 : location_info := LocationInfo file_0 99 11 99 14.
  Definition loc_116 : location_info := LocationInfo file_0 99 11 99 14.
  Definition loc_117 : location_info := LocationInfo file_0 98 4 98 13.
  Definition loc_118 : location_info := LocationInfo file_0 98 4 98 13.
  Definition loc_119 : location_info := LocationInfo file_0 98 14 98 22.
  Definition loc_120 : location_info := LocationInfo file_0 98 15 98 22.
  Definition loc_121 : location_info := LocationInfo file_0 98 15 98 16.
  Definition loc_122 : location_info := LocationInfo file_0 98 15 98 16.
  Definition loc_123 : location_info := LocationInfo file_0 96 17 96 35.
  Definition loc_124 : location_info := LocationInfo file_0 96 17 96 35.
  Definition loc_125 : location_info := LocationInfo file_0 96 17 96 33.
  Definition loc_126 : location_info := LocationInfo file_0 96 17 96 18.
  Definition loc_127 : location_info := LocationInfo file_0 96 17 96 18.
  Definition loc_130 : location_info := LocationInfo file_0 92 40 95 5.
  Definition loc_131 : location_info := LocationInfo file_0 93 8 93 32.
  Definition loc_132 : location_info := LocationInfo file_0 94 8 94 32.
  Definition loc_133 : location_info := LocationInfo file_0 94 8 94 26.
  Definition loc_134 : location_info := LocationInfo file_0 94 8 94 24.
  Definition loc_135 : location_info := LocationInfo file_0 94 8 94 9.
  Definition loc_136 : location_info := LocationInfo file_0 94 8 94 9.
  Definition loc_137 : location_info := LocationInfo file_0 94 8 94 31.
  Definition loc_138 : location_info := LocationInfo file_0 94 8 94 26.
  Definition loc_139 : location_info := LocationInfo file_0 94 8 94 26.
  Definition loc_140 : location_info := LocationInfo file_0 94 8 94 24.
  Definition loc_141 : location_info := LocationInfo file_0 94 8 94 9.
  Definition loc_142 : location_info := LocationInfo file_0 94 8 94 9.
  Definition loc_143 : location_info := LocationInfo file_0 94 30 94 31.
  Definition loc_144 : location_info := LocationInfo file_0 93 8 93 26.
  Definition loc_145 : location_info := LocationInfo file_0 93 8 93 24.
  Definition loc_146 : location_info := LocationInfo file_0 93 8 93 9.
  Definition loc_147 : location_info := LocationInfo file_0 93 8 93 9.
  Definition loc_148 : location_info := LocationInfo file_0 93 8 93 31.
  Definition loc_149 : location_info := LocationInfo file_0 93 8 93 26.
  Definition loc_150 : location_info := LocationInfo file_0 93 8 93 26.
  Definition loc_151 : location_info := LocationInfo file_0 93 8 93 24.
  Definition loc_152 : location_info := LocationInfo file_0 93 8 93 9.
  Definition loc_153 : location_info := LocationInfo file_0 93 8 93 9.
  Definition loc_154 : location_info := LocationInfo file_0 93 30 93 31.
  Definition loc_156 : location_info := LocationInfo file_0 92 8 92 38.
  Definition loc_157 : location_info := LocationInfo file_0 92 8 92 26.
  Definition loc_158 : location_info := LocationInfo file_0 92 8 92 26.
  Definition loc_159 : location_info := LocationInfo file_0 92 8 92 24.
  Definition loc_160 : location_info := LocationInfo file_0 92 8 92 9.
  Definition loc_161 : location_info := LocationInfo file_0 92 8 92 9.
  Definition loc_162 : location_info := LocationInfo file_0 92 29 92 38.
  Definition loc_163 : location_info := LocationInfo file_0 92 37 92 38.
  Definition loc_164 : location_info := LocationInfo file_0 90 29 90 48.
  Definition loc_165 : location_info := LocationInfo file_0 90 30 90 48.
  Definition loc_166 : location_info := LocationInfo file_0 90 31 90 32.
  Definition loc_167 : location_info := LocationInfo file_0 90 31 90 32.
  Definition loc_168 : location_info := LocationInfo file_0 89 4 89 11.
  Definition loc_169 : location_info := LocationInfo file_0 89 4 89 11.
  Definition loc_170 : location_info := LocationInfo file_0 89 12 89 20.
  Definition loc_171 : location_info := LocationInfo file_0 89 13 89 20.
  Definition loc_172 : location_info := LocationInfo file_0 89 13 89 14.
  Definition loc_173 : location_info := LocationInfo file_0 89 13 89 14.

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
      (None, mk_layout 7%nat 0%nat);
      (Some "locked_int", it_layout size_t);
      (Some "locked_struct", layout_of struct_lock_test_inner)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [init]. *)
  Definition impl_init (sl_init : loc): function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_27 ((LocInfoE loc_28 (!{LPtr} (LocInfoE loc_29 ("t")))) at{struct_lock_test} "outside") <-{ it_layout size_t }
          LocInfoE loc_30 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_30 (i2v 0 i32))) ;
        locinfo: loc_3 ;
        LocInfoE loc_23 ((LocInfoE loc_24 (!{LPtr} (LocInfoE loc_25 ("t")))) at{struct_lock_test} "locked_int") <-{ it_layout size_t }
          LocInfoE loc_26 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_26 (i2v 0 i32))) ;
        locinfo: loc_4 ;
        LocInfoE loc_18 ((LocInfoE loc_19 ((LocInfoE loc_20 (!{LPtr} (LocInfoE loc_21 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a") <-{ it_layout size_t }
          LocInfoE loc_22 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_22 (i2v 0 i32))) ;
        locinfo: loc_5 ;
        LocInfoE loc_13 ((LocInfoE loc_14 ((LocInfoE loc_15 (!{LPtr} (LocInfoE loc_16 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b") <-{ it_layout size_t }
          LocInfoE loc_17 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_17 (i2v 10 i32))) ;
        locinfo: loc_6 ;
        "_" <- LocInfoE loc_8 (sl_init) with
          [ LocInfoE loc_9 (&(LocInfoE loc_10 ((LocInfoE loc_11 (!{LPtr} (LocInfoE loc_12 ("t")))) at{struct_lock_test} "lock"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [write_outside]. *)
  Definition impl_write_outside : function := {|
    f_args := [
      ("t", LPtr);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_33 ;
        LocInfoE loc_34 ((LocInfoE loc_35 (!{LPtr} (LocInfoE loc_36 ("t")))) at{struct_lock_test} "outside") <-{ it_layout size_t }
          LocInfoE loc_37 (use{it_layout size_t} (LocInfoE loc_38 ("n"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [read_outside]. *)
  Definition impl_read_outside : function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{it_layout size_t} (LocInfoE loc_43 ((LocInfoE loc_44 (!{LPtr} (LocInfoE loc_45 ("t")))) at{struct_lock_test} "outside"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [write_locked]. *)
  Definition impl_write_locked (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("t", LPtr);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_48 ;
        "_" <- LocInfoE loc_69 (sl_lock) with
          [ LocInfoE loc_70 (&(LocInfoE loc_71 ((LocInfoE loc_72 (!{LPtr} (LocInfoE loc_73 ("t")))) at{struct_lock_test} "lock"))) ] ;
        locinfo: loc_49 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_64 (&(LocInfoE loc_65 ((LocInfoE loc_66 (!{LPtr} (LocInfoE loc_67 ("t")))) at{struct_lock_test} "locked_int")))) ;
        locinfo: loc_51 ;
        LocInfoE loc_59 ((LocInfoE loc_60 (!{LPtr} (LocInfoE loc_61 ("t")))) at{struct_lock_test} "locked_int") <-{ it_layout size_t }
          LocInfoE loc_62 (use{it_layout size_t} (LocInfoE loc_63 ("n"))) ;
        locinfo: loc_52 ;
        "_" <- LocInfoE loc_54 (sl_unlock) with
          [ LocInfoE loc_55 (AnnotExpr 1%nat LockA (LocInfoE loc_55 (&(LocInfoE loc_56 ((LocInfoE loc_57 (!{LPtr} (LocInfoE loc_58 ("t")))) at{struct_lock_test} "lock"))))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [read_locked]. *)
  Definition impl_read_locked (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
      ("ret", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_76 ;
        "_" <- LocInfoE loc_101 (sl_lock) with
          [ LocInfoE loc_102 (&(LocInfoE loc_103 ((LocInfoE loc_104 (!{LPtr} (LocInfoE loc_105 ("t")))) at{struct_lock_test} "lock"))) ] ;
        locinfo: loc_77 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_96 (&(LocInfoE loc_97 ((LocInfoE loc_98 (!{LPtr} (LocInfoE loc_99 ("t")))) at{struct_lock_test} "locked_int")))) ;
        "ret" <-{ it_layout size_t }
          LocInfoE loc_90 (use{it_layout size_t} (LocInfoE loc_91 ((LocInfoE loc_92 (!{LPtr} (LocInfoE loc_93 ("t")))) at{struct_lock_test} "locked_int"))) ;
        locinfo: loc_80 ;
        "_" <- LocInfoE loc_85 (sl_unlock) with
          [ LocInfoE loc_86 (AnnotExpr 1%nat LockA (LocInfoE loc_86 (&(LocInfoE loc_87 ((LocInfoE loc_88 (!{LPtr} (LocInfoE loc_89 ("t")))) at{struct_lock_test} "lock"))))) ] ;
        locinfo: loc_81 ;
        Return (LocInfoE loc_82 (use{it_layout size_t} (LocInfoE loc_83 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [increment]. *)
  Definition impl_increment (sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("t", LPtr)
    ];
    f_local_vars := [
      ("ret", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_108 ;
        "_" <- LocInfoE loc_169 (sl_lock) with
          [ LocInfoE loc_170 (&(LocInfoE loc_171 ((LocInfoE loc_172 (!{LPtr} (LocInfoE loc_173 ("t")))) at{struct_lock_test} "lock"))) ] ;
        locinfo: loc_109 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_164 (&(LocInfoE loc_165 ((LocInfoE loc_166 (!{LPtr} (LocInfoE loc_167 ("t")))) at{struct_lock_test} "locked_struct")))) ;
        locinfo: loc_156 ;
        if: LocInfoE loc_156 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_156 ((LocInfoE loc_157 (use{it_layout size_t} (LocInfoE loc_158 ((LocInfoE loc_159 ((LocInfoE loc_160 (!{LPtr} (LocInfoE loc_161 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b")))) >{IntOp size_t, IntOp size_t} (LocInfoE loc_162 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_163 (i2v 0 i32)))))))
        then
        locinfo: loc_131 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "ret" <-{ it_layout size_t }
          LocInfoE loc_123 (use{it_layout size_t} (LocInfoE loc_124 ((LocInfoE loc_125 ((LocInfoE loc_126 (!{LPtr} (LocInfoE loc_127 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a"))) ;
        locinfo: loc_113 ;
        "_" <- LocInfoE loc_118 (sl_unlock) with
          [ LocInfoE loc_119 (AnnotExpr 1%nat LockA (LocInfoE loc_119 (&(LocInfoE loc_120 ((LocInfoE loc_121 (!{LPtr} (LocInfoE loc_122 ("t")))) at{struct_lock_test} "lock"))))) ] ;
        locinfo: loc_114 ;
        Return (LocInfoE loc_115 (use{it_layout size_t} (LocInfoE loc_116 ("ret"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_131 ;
        LocInfoE loc_144 ((LocInfoE loc_145 ((LocInfoE loc_146 (!{LPtr} (LocInfoE loc_147 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a") <-{ it_layout size_t }
          LocInfoE loc_148 ((LocInfoE loc_149 (use{it_layout size_t} (LocInfoE loc_150 ((LocInfoE loc_151 ((LocInfoE loc_152 (!{LPtr} (LocInfoE loc_153 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "a")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_154 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_154 (i2v 1 i32))))) ;
        locinfo: loc_132 ;
        LocInfoE loc_133 ((LocInfoE loc_134 ((LocInfoE loc_135 (!{LPtr} (LocInfoE loc_136 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b") <-{ it_layout size_t }
          LocInfoE loc_137 ((LocInfoE loc_138 (use{it_layout size_t} (LocInfoE loc_139 ((LocInfoE loc_140 ((LocInfoE loc_141 (!{LPtr} (LocInfoE loc_142 ("t")))) at{struct_lock_test} "locked_struct")) at{struct_lock_test_inner} "b")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_143 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_143 (i2v 1 i32))))) ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
