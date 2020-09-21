From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t04_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 13 2 45 3.
  Definition loc_3 : location_info := LocationInfo file_0 13 2 45 3.
  Definition loc_4 : location_info := LocationInfo file_0 13 11 45 3.
  Definition loc_5 : location_info := LocationInfo file_0 14 4 14 35.
  Definition loc_6 : location_info := LocationInfo file_0 15 4 15 53.
  Definition loc_7 : location_info := LocationInfo file_0 15 53 15 5.
  Definition loc_8 : location_info := LocationInfo file_0 18 4 18 48.
  Definition loc_9 : location_info := LocationInfo file_0 23 4 41 5.
  Definition loc_10 : location_info := LocationInfo file_0 43 4 43 13.
  Definition loc_11 : location_info := LocationInfo file_0 43 13 43 5.
  Definition loc_12 : location_info := LocationInfo file_0 44 4 44 37.
  Definition loc_13 : location_info := LocationInfo file_0 13 2 45 3.
  Definition loc_14 : location_info := LocationInfo file_0 13 2 45 3.
  Definition loc_15 : location_info := LocationInfo file_0 44 4 44 13.
  Definition loc_16 : location_info := LocationInfo file_0 44 4 44 13.
  Definition loc_17 : location_info := LocationInfo file_0 44 14 44 35.
  Definition loc_18 : location_info := LocationInfo file_0 44 15 44 35.
  Definition loc_19 : location_info := LocationInfo file_0 44 15 44 30.
  Definition loc_20 : location_info := LocationInfo file_0 43 4 43 12.
  Definition loc_21 : location_info := LocationInfo file_0 43 5 43 12.
  Definition loc_22 : location_info := LocationInfo file_0 43 7 43 11.
  Definition loc_23 : location_info := LocationInfo file_0 43 7 43 11.
  Definition loc_24 : location_info := LocationInfo file_0 23 4 41 5.
  Definition loc_25 : location_info := LocationInfo file_0 23 35 41 5.
  Definition loc_26 : location_info := LocationInfo file_0 24 6 24 32.
  Definition loc_27 : location_info := LocationInfo file_0 26 6 31 7.
  Definition loc_28 : location_info := LocationInfo file_0 32 6 38 7.
  Definition loc_29 : location_info := LocationInfo file_0 40 6 40 24.
  Definition loc_30 : location_info := LocationInfo file_0 23 4 41 5.
  Definition loc_31 : location_info := LocationInfo file_0 23 4 41 5.
  Definition loc_32 : location_info := LocationInfo file_0 40 6 40 10.
  Definition loc_33 : location_info := LocationInfo file_0 40 13 40 23.
  Definition loc_34 : location_info := LocationInfo file_0 40 14 40 23.
  Definition loc_35 : location_info := LocationInfo file_0 40 14 40 17.
  Definition loc_36 : location_info := LocationInfo file_0 40 14 40 17.
  Definition loc_37 : location_info := LocationInfo file_0 32 57 38 7.
  Definition loc_38 : location_info := LocationInfo file_0 33 8 33 26.
  Definition loc_39 : location_info := LocationInfo file_0 34 8 34 54.
  Definition loc_40 : location_info := LocationInfo file_0 35 8 35 17.
  Definition loc_41 : location_info := LocationInfo file_0 35 17 35 9.
  Definition loc_42 : location_info := LocationInfo file_0 36 8 36 41.
  Definition loc_43 : location_info := LocationInfo file_0 37 8 37 19.
  Definition loc_44 : location_info := LocationInfo file_0 37 15 37 18.
  Definition loc_45 : location_info := LocationInfo file_0 37 15 37 18.
  Definition loc_46 : location_info := LocationInfo file_0 36 8 36 17.
  Definition loc_47 : location_info := LocationInfo file_0 36 8 36 17.
  Definition loc_48 : location_info := LocationInfo file_0 36 18 36 39.
  Definition loc_49 : location_info := LocationInfo file_0 36 19 36 39.
  Definition loc_50 : location_info := LocationInfo file_0 36 19 36 34.
  Definition loc_51 : location_info := LocationInfo file_0 35 8 35 16.
  Definition loc_52 : location_info := LocationInfo file_0 35 9 35 16.
  Definition loc_53 : location_info := LocationInfo file_0 35 11 35 15.
  Definition loc_54 : location_info := LocationInfo file_0 35 11 35 15.
  Definition loc_55 : location_info := LocationInfo file_0 34 20 34 53.
  Definition loc_56 : location_info := LocationInfo file_0 34 21 34 40.
  Definition loc_57 : location_info := LocationInfo file_0 34 37 34 40.
  Definition loc_58 : location_info := LocationInfo file_0 34 37 34 40.
  Definition loc_59 : location_info := LocationInfo file_0 34 43 34 52.
  Definition loc_60 : location_info := LocationInfo file_0 34 43 34 52.
  Definition loc_61 : location_info := LocationInfo file_0 34 43 34 46.
  Definition loc_62 : location_info := LocationInfo file_0 34 43 34 46.
  Definition loc_65 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_66 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_67 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_68 : location_info := LocationInfo file_0 33 8 33 25.
  Definition loc_69 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_70 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_71 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_72 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_73 : location_info := LocationInfo file_0 33 21 33 25.
  Definition loc_74 : location_info := LocationInfo file_0 33 21 33 25.
  Definition loc_76 : location_info := LocationInfo file_0 32 9 32 55.
  Definition loc_77 : location_info := LocationInfo file_0 32 9 32 18.
  Definition loc_78 : location_info := LocationInfo file_0 32 9 32 18.
  Definition loc_79 : location_info := LocationInfo file_0 32 9 32 12.
  Definition loc_80 : location_info := LocationInfo file_0 32 9 32 12.
  Definition loc_81 : location_info := LocationInfo file_0 32 22 32 55.
  Definition loc_82 : location_info := LocationInfo file_0 32 22 32 26.
  Definition loc_83 : location_info := LocationInfo file_0 32 22 32 26.
  Definition loc_84 : location_info := LocationInfo file_0 32 29 32 55.
  Definition loc_85 : location_info := LocationInfo file_0 26 28 31 7.
  Definition loc_86 : location_info := LocationInfo file_0 27 8 27 26.
  Definition loc_87 : location_info := LocationInfo file_0 28 8 28 17.
  Definition loc_88 : location_info := LocationInfo file_0 28 17 28 9.
  Definition loc_89 : location_info := LocationInfo file_0 29 8 29 41.
  Definition loc_90 : location_info := LocationInfo file_0 30 8 30 19.
  Definition loc_91 : location_info := LocationInfo file_0 30 15 30 18.
  Definition loc_92 : location_info := LocationInfo file_0 30 15 30 18.
  Definition loc_93 : location_info := LocationInfo file_0 29 8 29 17.
  Definition loc_94 : location_info := LocationInfo file_0 29 8 29 17.
  Definition loc_95 : location_info := LocationInfo file_0 29 18 29 39.
  Definition loc_96 : location_info := LocationInfo file_0 29 19 29 39.
  Definition loc_97 : location_info := LocationInfo file_0 29 19 29 34.
  Definition loc_98 : location_info := LocationInfo file_0 28 8 28 16.
  Definition loc_99 : location_info := LocationInfo file_0 28 9 28 16.
  Definition loc_100 : location_info := LocationInfo file_0 28 11 28 15.
  Definition loc_101 : location_info := LocationInfo file_0 28 11 28 15.
  Definition loc_102 : location_info := LocationInfo file_0 27 8 27 13.
  Definition loc_103 : location_info := LocationInfo file_0 27 9 27 13.
  Definition loc_104 : location_info := LocationInfo file_0 27 9 27 13.
  Definition loc_105 : location_info := LocationInfo file_0 27 16 27 25.
  Definition loc_106 : location_info := LocationInfo file_0 27 16 27 25.
  Definition loc_107 : location_info := LocationInfo file_0 27 16 27 19.
  Definition loc_108 : location_info := LocationInfo file_0 27 16 27 19.
  Definition loc_110 : location_info := LocationInfo file_0 26 9 26 26.
  Definition loc_111 : location_info := LocationInfo file_0 26 9 26 18.
  Definition loc_112 : location_info := LocationInfo file_0 26 9 26 18.
  Definition loc_113 : location_info := LocationInfo file_0 26 9 26 12.
  Definition loc_114 : location_info := LocationInfo file_0 26 9 26 12.
  Definition loc_115 : location_info := LocationInfo file_0 26 22 26 26.
  Definition loc_116 : location_info := LocationInfo file_0 26 22 26 26.
  Definition loc_117 : location_info := LocationInfo file_0 24 26 24 31.
  Definition loc_118 : location_info := LocationInfo file_0 24 26 24 31.
  Definition loc_119 : location_info := LocationInfo file_0 24 27 24 31.
  Definition loc_120 : location_info := LocationInfo file_0 24 27 24 31.
  Definition loc_123 : location_info := LocationInfo file_0 23 10 23 33.
  Definition loc_124 : location_info := LocationInfo file_0 23 10 23 15.
  Definition loc_125 : location_info := LocationInfo file_0 23 10 23 15.
  Definition loc_126 : location_info := LocationInfo file_0 23 11 23 15.
  Definition loc_127 : location_info := LocationInfo file_0 23 11 23 15.
  Definition loc_128 : location_info := LocationInfo file_0 23 19 23 33.
  Definition loc_129 : location_info := LocationInfo file_0 18 26 18 47.
  Definition loc_130 : location_info := LocationInfo file_0 18 27 18 47.
  Definition loc_131 : location_info := LocationInfo file_0 18 27 18 42.
  Definition loc_134 : location_info := LocationInfo file_0 15 29 15 52.
  Definition loc_135 : location_info := LocationInfo file_0 15 30 15 52.
  Definition loc_136 : location_info := LocationInfo file_0 15 31 15 46.
  Definition loc_137 : location_info := LocationInfo file_0 14 4 14 11.
  Definition loc_138 : location_info := LocationInfo file_0 14 4 14 11.
  Definition loc_139 : location_info := LocationInfo file_0 14 12 14 33.
  Definition loc_140 : location_info := LocationInfo file_0 14 13 14 33.
  Definition loc_141 : location_info := LocationInfo file_0 14 13 14 28.
  Definition loc_142 : location_info := LocationInfo file_0 13 8 13 9.
  Definition loc_145 : location_info := LocationInfo file_0 51 2 54 3.
  Definition loc_146 : location_info := LocationInfo file_0 56 2 56 34.
  Definition loc_147 : location_info := LocationInfo file_0 57 2 57 21.
  Definition loc_148 : location_info := LocationInfo file_0 59 2 59 33.
  Definition loc_149 : location_info := LocationInfo file_0 60 2 60 51.
  Definition loc_150 : location_info := LocationInfo file_0 60 51 60 3.
  Definition loc_151 : location_info := LocationInfo file_0 62 2 62 37.
  Definition loc_152 : location_info := LocationInfo file_0 63 2 63 31.
  Definition loc_153 : location_info := LocationInfo file_0 65 2 65 35.
  Definition loc_154 : location_info := LocationInfo file_0 65 2 65 11.
  Definition loc_155 : location_info := LocationInfo file_0 65 2 65 11.
  Definition loc_156 : location_info := LocationInfo file_0 65 12 65 33.
  Definition loc_157 : location_info := LocationInfo file_0 65 13 65 33.
  Definition loc_158 : location_info := LocationInfo file_0 65 13 65 28.
  Definition loc_159 : location_info := LocationInfo file_0 63 2 63 22.
  Definition loc_160 : location_info := LocationInfo file_0 63 2 63 17.
  Definition loc_161 : location_info := LocationInfo file_0 63 25 63 30.
  Definition loc_162 : location_info := LocationInfo file_0 63 25 63 30.
  Definition loc_163 : location_info := LocationInfo file_0 62 2 62 13.
  Definition loc_164 : location_info := LocationInfo file_0 62 2 62 7.
  Definition loc_165 : location_info := LocationInfo file_0 62 2 62 7.
  Definition loc_166 : location_info := LocationInfo file_0 62 16 62 36.
  Definition loc_167 : location_info := LocationInfo file_0 62 16 62 36.
  Definition loc_168 : location_info := LocationInfo file_0 62 16 62 31.
  Definition loc_169 : location_info := LocationInfo file_0 60 27 60 50.
  Definition loc_170 : location_info := LocationInfo file_0 60 28 60 50.
  Definition loc_171 : location_info := LocationInfo file_0 60 29 60 44.
  Definition loc_172 : location_info := LocationInfo file_0 59 2 59 9.
  Definition loc_173 : location_info := LocationInfo file_0 59 2 59 9.
  Definition loc_174 : location_info := LocationInfo file_0 59 10 59 31.
  Definition loc_175 : location_info := LocationInfo file_0 59 11 59 31.
  Definition loc_176 : location_info := LocationInfo file_0 59 11 59 26.
  Definition loc_177 : location_info := LocationInfo file_0 57 2 57 13.
  Definition loc_178 : location_info := LocationInfo file_0 57 2 57 7.
  Definition loc_179 : location_info := LocationInfo file_0 57 2 57 7.
  Definition loc_180 : location_info := LocationInfo file_0 57 16 57 20.
  Definition loc_181 : location_info := LocationInfo file_0 57 16 57 20.
  Definition loc_182 : location_info := LocationInfo file_0 56 30 56 33.
  Definition loc_183 : location_info := LocationInfo file_0 56 30 56 33.
  Definition loc_186 : location_info := LocationInfo file_0 51 41 54 3.
  Definition loc_187 : location_info := LocationInfo file_0 53 4 53 11.
  Definition loc_190 : location_info := LocationInfo file_0 51 6 51 39.
  Definition loc_191 : location_info := LocationInfo file_0 51 6 51 10.
  Definition loc_192 : location_info := LocationInfo file_0 51 6 51 10.
  Definition loc_193 : location_info := LocationInfo file_0 51 13 51 39.
  Definition loc_196 : location_info := LocationInfo file_0 81 2 81 25.
  Definition loc_197 : location_info := LocationInfo file_0 81 9 81 24.
  Definition loc_198 : location_info := LocationInfo file_0 81 9 81 14.
  Definition loc_199 : location_info := LocationInfo file_0 81 9 81 14.
  Definition loc_200 : location_info := LocationInfo file_0 81 15 81 23.
  Definition loc_201 : location_info := LocationInfo file_0 81 15 81 16.
  Definition loc_202 : location_info := LocationInfo file_0 81 15 81 16.
  Definition loc_203 : location_info := LocationInfo file_0 81 19 81 23.
  Definition loc_204 : location_info := LocationInfo file_0 81 19 81 23.
  Definition loc_207 : location_info := LocationInfo file_0 86 2 86 22.
  Definition loc_208 : location_info := LocationInfo file_0 86 2 86 6.
  Definition loc_209 : location_info := LocationInfo file_0 86 2 86 6.
  Definition loc_210 : location_info := LocationInfo file_0 86 7 86 15.
  Definition loc_211 : location_info := LocationInfo file_0 86 7 86 8.
  Definition loc_212 : location_info := LocationInfo file_0 86 7 86 8.
  Definition loc_213 : location_info := LocationInfo file_0 86 11 86 15.
  Definition loc_214 : location_info := LocationInfo file_0 86 11 86 15.
  Definition loc_215 : location_info := LocationInfo file_0 86 17 86 20.
  Definition loc_216 : location_info := LocationInfo file_0 86 17 86 20.
  Definition loc_219 : location_info := LocationInfo file_0 69 2 69 33.
  Definition loc_220 : location_info := LocationInfo file_0 70 2 70 40.
  Definition loc_221 : location_info := LocationInfo file_0 74 2 74 12.
  Definition loc_222 : location_info := LocationInfo file_0 74 12 74 13.
  Definition loc_223 : location_info := LocationInfo file_0 76 2 76 49.
  Definition loc_224 : location_info := LocationInfo file_0 76 49 76 3.
  Definition loc_225 : location_info := LocationInfo file_0 76 30 76 48.
  Definition loc_226 : location_info := LocationInfo file_0 76 31 76 48.
  Definition loc_227 : location_info := LocationInfo file_0 74 2 74 12.
  Definition loc_228 : location_info := LocationInfo file_0 74 10 74 12.
  Definition loc_229 : location_info := LocationInfo file_0 74 2 74 12.
  Definition loc_230 : location_info := LocationInfo file_0 74 2 74 12.
  Definition loc_231 : location_info := LocationInfo file_0 74 8 74 9.
  Definition loc_232 : location_info := LocationInfo file_0 70 2 70 22.
  Definition loc_233 : location_info := LocationInfo file_0 70 2 70 17.
  Definition loc_234 : location_info := LocationInfo file_0 70 25 70 39.
  Definition loc_235 : location_info := LocationInfo file_0 69 2 69 9.
  Definition loc_236 : location_info := LocationInfo file_0 69 2 69 9.
  Definition loc_237 : location_info := LocationInfo file_0 69 10 69 31.
  Definition loc_238 : location_info := LocationInfo file_0 69 11 69 31.
  Definition loc_239 : location_info := LocationInfo file_0 69 11 69 26.

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

  (* Definition of function [alloc]. *)
  Definition impl_alloc (allocator_state sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", LPtr);
      ("cur", LPtr);
      ("ret", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_142 ;
        if: LocInfoE loc_142 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_142 (i2v 1 i32)))
        then
        locinfo: loc_5 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_29 ;
        Goto "#8"
      ]> $
      <[ "#11" :=
        locinfo: loc_86 ;
        LocInfoE loc_103 (!{LPtr} (LocInfoE loc_104 ("prev"))) <-{ LPtr }
          LocInfoE loc_105 (use{LPtr} (LocInfoE loc_106 ((LocInfoE loc_107 (!{LPtr} (LocInfoE loc_108 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_87 ;
        expr: (LocInfoE loc_98 (&(LocInfoE loc_100 (!{LPtr} (LocInfoE loc_101 ("prev")))))) ;
        locinfo: loc_89 ;
        "_" <- LocInfoE loc_94 (sl_unlock) with
          [ LocInfoE loc_95 (AnnotExpr 1%nat LockA (LocInfoE loc_95 (&(LocInfoE loc_96 ((LocInfoE loc_97 (allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
        locinfo: loc_90 ;
        Return (LocInfoE loc_91 (use{LPtr} (LocInfoE loc_92 ("cur"))))
      ]> $
      <[ "#12" :=
        locinfo: loc_76 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_5 ;
        "_" <- LocInfoE loc_138 (sl_lock) with
          [ LocInfoE loc_139 (&(LocInfoE loc_140 ((LocInfoE loc_141 (allocator_state)) at{struct_alloc_state} "lock"))) ] ;
        locinfo: loc_6 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_134 (&(LocInfoE loc_135 ((LocInfoE loc_136 (allocator_state)) at{struct_alloc_state} "data")))) ;
        "prev" <-{ LPtr }
          LocInfoE loc_129 (&(LocInfoE loc_130 ((LocInfoE loc_131 (allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_9 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_123 ;
        if: LocInfoE loc_123 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_123 ((LocInfoE loc_124 (use{LPtr} (LocInfoE loc_126 (!{LPtr} (LocInfoE loc_127 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_128 (NULL)))))
        then
        Goto "#5"
        else
        locinfo: loc_10 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        "cur" <-{ LPtr }
          LocInfoE loc_117 (use{LPtr} (LocInfoE loc_119 (!{LPtr} (LocInfoE loc_120 ("prev"))))) ;
        locinfo: loc_110 ;
        if: LocInfoE loc_110 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_110 ((LocInfoE loc_111 (use{it_layout size_t} (LocInfoE loc_112 ((LocInfoE loc_113 (!{LPtr} (LocInfoE loc_114 ("cur")))) at{struct_alloc_entry} "size")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_115 (use{it_layout size_t} (LocInfoE loc_116 ("size")))))))
        then
        locinfo: loc_86 ;
          Goto "#11"
        else
        locinfo: loc_76 ;
          Goto "#12"
      ]> $
      <[ "#6" :=
        locinfo: loc_10 ;
        expr: (LocInfoE loc_20 (&(LocInfoE loc_22 (!{LPtr} (LocInfoE loc_23 ("prev")))))) ;
        locinfo: loc_12 ;
        "_" <- LocInfoE loc_16 (sl_unlock) with
          [ LocInfoE loc_17 (AnnotExpr 1%nat LockA (LocInfoE loc_17 (&(LocInfoE loc_18 ((LocInfoE loc_19 (allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
        locinfo: loc_13 ;
        Goto "continue2"
      ]> $
      <[ "#7" :=
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout size_t} (LocInfoE loc_78 ((LocInfoE loc_79 (!{LPtr} (LocInfoE loc_80 ("cur")))) at{struct_alloc_entry} "size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_81 ((LocInfoE loc_82 (use{it_layout size_t} (LocInfoE loc_83 ("size")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_84 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))))
        then
        locinfo: loc_38 ;
          Goto "#9"
        else
        locinfo: loc_29 ;
          Goto "#10"
      ]> $
      <[ "#8" :=
        locinfo: loc_29 ;
        LocInfoE loc_32 ("prev") <-{ LPtr }
          LocInfoE loc_33 (&(LocInfoE loc_34 ((LocInfoE loc_35 (!{LPtr} (LocInfoE loc_36 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_30 ;
        Goto "continue4"
      ]> $
      <[ "#9" :=
        locinfo: loc_38 ;
        LocInfoE loc_65 ((LocInfoE loc_66 (!{LPtr} (LocInfoE loc_67 ("cur")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_68 ((LocInfoE loc_69 (use{it_layout size_t} (LocInfoE loc_70 ((LocInfoE loc_71 (!{LPtr} (LocInfoE loc_72 ("cur")))) at{struct_alloc_entry} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_73 (use{it_layout size_t} (LocInfoE loc_74 ("size"))))) ;
        "ret" <-{ LPtr }
          LocInfoE loc_55 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_55 ((LocInfoE loc_56 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_57 (use{LPtr} (LocInfoE loc_58 ("cur")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_59 (use{it_layout size_t} (LocInfoE loc_60 ((LocInfoE loc_61 (!{LPtr} (LocInfoE loc_62 ("cur")))) at{struct_alloc_entry} "size"))))))) ;
        locinfo: loc_40 ;
        expr: (LocInfoE loc_51 (&(LocInfoE loc_53 (!{LPtr} (LocInfoE loc_54 ("prev")))))) ;
        locinfo: loc_42 ;
        "_" <- LocInfoE loc_47 (sl_unlock) with
          [ LocInfoE loc_48 (AnnotExpr 1%nat LockA (LocInfoE loc_48 (&(LocInfoE loc_49 ((LocInfoE loc_50 (allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{LPtr} (LocInfoE loc_45 ("ret"))))
      ]> $
      <[ "continue2" :=
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "continue4" :=
        locinfo: loc_9 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [free]. *)
  Definition impl_free (allocator_state sl_lock sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("ptr", LPtr)
    ];
    f_local_vars := [
      ("entry", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_190 ;
        if: LocInfoE loc_190 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_190 ((LocInfoE loc_191 (use{it_layout size_t} (LocInfoE loc_192 ("size")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_193 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))
        then
        locinfo: loc_187 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ LPtr }
          LocInfoE loc_182 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_182 (use{LPtr} (LocInfoE loc_183 ("ptr"))))) ;
        locinfo: loc_147 ;
        LocInfoE loc_177 ((LocInfoE loc_178 (!{LPtr} (LocInfoE loc_179 ("entry")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_180 (use{it_layout size_t} (LocInfoE loc_181 ("size"))) ;
        locinfo: loc_148 ;
        "_" <- LocInfoE loc_173 (sl_lock) with
          [ LocInfoE loc_174 (&(LocInfoE loc_175 ((LocInfoE loc_176 (allocator_state)) at{struct_alloc_state} "lock"))) ] ;
        locinfo: loc_149 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_169 (&(LocInfoE loc_170 ((LocInfoE loc_171 (allocator_state)) at{struct_alloc_state} "data")))) ;
        locinfo: loc_151 ;
        LocInfoE loc_163 ((LocInfoE loc_164 (!{LPtr} (LocInfoE loc_165 ("entry")))) at{struct_alloc_entry} "next") <-{ LPtr }
          LocInfoE loc_166 (use{LPtr} (LocInfoE loc_167 ((LocInfoE loc_168 (allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_152 ;
        LocInfoE loc_159 ((LocInfoE loc_160 (allocator_state)) at{struct_alloc_state} "data") <-{ LPtr }
          LocInfoE loc_161 (use{LPtr} (LocInfoE loc_162 ("entry"))) ;
        locinfo: loc_153 ;
        "_" <- LocInfoE loc_155 (sl_unlock) with
          [ LocInfoE loc_156 (AnnotExpr 1%nat LockA (LocInfoE loc_156 (&(LocInfoE loc_157 ((LocInfoE loc_158 (allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_187 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_array]. *)
  Definition impl_alloc_array (alloc : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_197 ;
        "$0" <- LocInfoE loc_199 (alloc) with
          [ LocInfoE loc_200 ((LocInfoE loc_201 (use{it_layout size_t} (LocInfoE loc_202 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_203 (use{it_layout size_t} (LocInfoE loc_204 ("size"))))) ] ;
        locinfo: loc_196 ;
        Return (LocInfoE loc_197 ("$0"))
      ]> $∅
    )%E
  |}.

  (* Definition of function [free_array]. *)
  Definition impl_free_array (free : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("n", it_layout size_t);
      ("ptr", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_207 ;
        "_" <- LocInfoE loc_209 (free) with
          [ LocInfoE loc_210 ((LocInfoE loc_211 (use{it_layout size_t} (LocInfoE loc_212 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_213 (use{it_layout size_t} (LocInfoE loc_214 ("size"))))) ;
          LocInfoE loc_215 (use{LPtr} (LocInfoE loc_216 ("ptr"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_alloc]. *)
  Definition impl_init_alloc (allocator_state sl_init : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_219 ;
        "_" <- LocInfoE loc_236 (sl_init) with
          [ LocInfoE loc_237 (&(LocInfoE loc_238 ((LocInfoE loc_239 (allocator_state)) at{struct_alloc_state} "lock"))) ] ;
        locinfo: loc_220 ;
        LocInfoE loc_232 ((LocInfoE loc_233 (allocator_state)) at{struct_alloc_state} "data") <-{ LPtr }
          LocInfoE loc_234 (NULL) ;
        locinfo: loc_221 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_231 ;
        if: LocInfoE loc_231 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_231 (i2v 0 i32)))
        then
        locinfo: loc_229 ;
          Goto "#2"
        else
        locinfo: loc_223 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_229 ;
        Goto "continue13"
      ]> $
      <[ "#3" :=
        locinfo: loc_223 ;
        annot: (ShareAnnot) ;
        expr: (LocInfoE loc_225 (&(LocInfoE loc_226 (allocator_state)))) ;
        Return (VOID)
      ]> $
      <[ "continue13" :=
        locinfo: loc_221 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
