From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t04_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 14 2 43 3.
  Definition loc_12 : location_info := LocationInfo file_1 14 2 43 3.
  Definition loc_13 : location_info := LocationInfo file_1 14 11 43 3.
  Definition loc_14 : location_info := LocationInfo file_1 15 4 15 35.
  Definition loc_15 : location_info := LocationInfo file_1 16 4 16 53.
  Definition loc_16 : location_info := LocationInfo file_1 16 53 16 5.
  Definition loc_17 : location_info := LocationInfo file_1 19 4 19 48.
  Definition loc_18 : location_info := LocationInfo file_1 24 4 40 5.
  Definition loc_19 : location_info := LocationInfo file_1 42 4 42 37.
  Definition loc_20 : location_info := LocationInfo file_1 14 2 43 3.
  Definition loc_21 : location_info := LocationInfo file_1 14 2 43 3.
  Definition loc_22 : location_info := LocationInfo file_1 42 4 42 13.
  Definition loc_23 : location_info := LocationInfo file_1 42 4 42 13.
  Definition loc_24 : location_info := LocationInfo file_1 42 14 42 35.
  Definition loc_25 : location_info := LocationInfo file_1 42 15 42 35.
  Definition loc_26 : location_info := LocationInfo file_1 42 15 42 30.
  Definition loc_27 : location_info := LocationInfo file_1 24 4 40 5.
  Definition loc_28 : location_info := LocationInfo file_1 24 35 40 5.
  Definition loc_29 : location_info := LocationInfo file_1 25 6 25 32.
  Definition loc_30 : location_info := LocationInfo file_1 27 6 31 7.
  Definition loc_31 : location_info := LocationInfo file_1 32 6 37 7.
  Definition loc_32 : location_info := LocationInfo file_1 39 6 39 24.
  Definition loc_33 : location_info := LocationInfo file_1 24 4 40 5.
  Definition loc_34 : location_info := LocationInfo file_1 24 4 40 5.
  Definition loc_35 : location_info := LocationInfo file_1 39 6 39 10.
  Definition loc_36 : location_info := LocationInfo file_1 39 13 39 23.
  Definition loc_37 : location_info := LocationInfo file_1 39 14 39 23.
  Definition loc_38 : location_info := LocationInfo file_1 39 14 39 17.
  Definition loc_39 : location_info := LocationInfo file_1 39 14 39 17.
  Definition loc_40 : location_info := LocationInfo file_1 32 57 37 7.
  Definition loc_41 : location_info := LocationInfo file_1 33 8 33 26.
  Definition loc_42 : location_info := LocationInfo file_1 34 8 34 54.
  Definition loc_43 : location_info := LocationInfo file_1 35 8 35 41.
  Definition loc_44 : location_info := LocationInfo file_1 36 8 36 19.
  Definition loc_45 : location_info := LocationInfo file_1 36 15 36 18.
  Definition loc_46 : location_info := LocationInfo file_1 36 15 36 18.
  Definition loc_47 : location_info := LocationInfo file_1 35 8 35 17.
  Definition loc_48 : location_info := LocationInfo file_1 35 8 35 17.
  Definition loc_49 : location_info := LocationInfo file_1 35 18 35 39.
  Definition loc_50 : location_info := LocationInfo file_1 35 19 35 39.
  Definition loc_51 : location_info := LocationInfo file_1 35 19 35 34.
  Definition loc_52 : location_info := LocationInfo file_1 34 20 34 53.
  Definition loc_53 : location_info := LocationInfo file_1 34 21 34 40.
  Definition loc_54 : location_info := LocationInfo file_1 34 37 34 40.
  Definition loc_55 : location_info := LocationInfo file_1 34 37 34 40.
  Definition loc_56 : location_info := LocationInfo file_1 34 43 34 52.
  Definition loc_57 : location_info := LocationInfo file_1 34 43 34 52.
  Definition loc_58 : location_info := LocationInfo file_1 34 43 34 46.
  Definition loc_59 : location_info := LocationInfo file_1 34 43 34 46.
  Definition loc_62 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_63 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_64 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_65 : location_info := LocationInfo file_1 33 8 33 25.
  Definition loc_66 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_67 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_68 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_69 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_70 : location_info := LocationInfo file_1 33 21 33 25.
  Definition loc_71 : location_info := LocationInfo file_1 33 21 33 25.
  Definition loc_73 : location_info := LocationInfo file_1 32 9 32 55.
  Definition loc_74 : location_info := LocationInfo file_1 32 9 32 18.
  Definition loc_75 : location_info := LocationInfo file_1 32 9 32 18.
  Definition loc_76 : location_info := LocationInfo file_1 32 9 32 12.
  Definition loc_77 : location_info := LocationInfo file_1 32 9 32 12.
  Definition loc_78 : location_info := LocationInfo file_1 32 22 32 55.
  Definition loc_79 : location_info := LocationInfo file_1 32 22 32 26.
  Definition loc_80 : location_info := LocationInfo file_1 32 22 32 26.
  Definition loc_81 : location_info := LocationInfo file_1 32 29 32 55.
  Definition loc_82 : location_info := LocationInfo file_1 27 28 31 7.
  Definition loc_83 : location_info := LocationInfo file_1 28 8 28 26.
  Definition loc_84 : location_info := LocationInfo file_1 29 8 29 41.
  Definition loc_85 : location_info := LocationInfo file_1 30 8 30 19.
  Definition loc_86 : location_info := LocationInfo file_1 30 15 30 18.
  Definition loc_87 : location_info := LocationInfo file_1 30 15 30 18.
  Definition loc_88 : location_info := LocationInfo file_1 29 8 29 17.
  Definition loc_89 : location_info := LocationInfo file_1 29 8 29 17.
  Definition loc_90 : location_info := LocationInfo file_1 29 18 29 39.
  Definition loc_91 : location_info := LocationInfo file_1 29 19 29 39.
  Definition loc_92 : location_info := LocationInfo file_1 29 19 29 34.
  Definition loc_93 : location_info := LocationInfo file_1 28 8 28 13.
  Definition loc_94 : location_info := LocationInfo file_1 28 9 28 13.
  Definition loc_95 : location_info := LocationInfo file_1 28 9 28 13.
  Definition loc_96 : location_info := LocationInfo file_1 28 16 28 25.
  Definition loc_97 : location_info := LocationInfo file_1 28 16 28 25.
  Definition loc_98 : location_info := LocationInfo file_1 28 16 28 19.
  Definition loc_99 : location_info := LocationInfo file_1 28 16 28 19.
  Definition loc_101 : location_info := LocationInfo file_1 27 9 27 26.
  Definition loc_102 : location_info := LocationInfo file_1 27 9 27 18.
  Definition loc_103 : location_info := LocationInfo file_1 27 9 27 18.
  Definition loc_104 : location_info := LocationInfo file_1 27 9 27 12.
  Definition loc_105 : location_info := LocationInfo file_1 27 9 27 12.
  Definition loc_106 : location_info := LocationInfo file_1 27 22 27 26.
  Definition loc_107 : location_info := LocationInfo file_1 27 22 27 26.
  Definition loc_108 : location_info := LocationInfo file_1 25 26 25 31.
  Definition loc_109 : location_info := LocationInfo file_1 25 26 25 31.
  Definition loc_110 : location_info := LocationInfo file_1 25 27 25 31.
  Definition loc_111 : location_info := LocationInfo file_1 25 27 25 31.
  Definition loc_114 : location_info := LocationInfo file_1 24 10 24 33.
  Definition loc_115 : location_info := LocationInfo file_1 24 10 24 15.
  Definition loc_116 : location_info := LocationInfo file_1 24 10 24 15.
  Definition loc_117 : location_info := LocationInfo file_1 24 11 24 15.
  Definition loc_118 : location_info := LocationInfo file_1 24 11 24 15.
  Definition loc_119 : location_info := LocationInfo file_1 24 19 24 33.
  Definition loc_120 : location_info := LocationInfo file_1 19 26 19 47.
  Definition loc_121 : location_info := LocationInfo file_1 19 27 19 47.
  Definition loc_122 : location_info := LocationInfo file_1 19 27 19 42.
  Definition loc_125 : location_info := LocationInfo file_1 16 29 16 52.
  Definition loc_126 : location_info := LocationInfo file_1 16 30 16 52.
  Definition loc_127 : location_info := LocationInfo file_1 16 31 16 46.
  Definition loc_128 : location_info := LocationInfo file_1 15 4 15 11.
  Definition loc_129 : location_info := LocationInfo file_1 15 4 15 11.
  Definition loc_130 : location_info := LocationInfo file_1 15 12 15 33.
  Definition loc_131 : location_info := LocationInfo file_1 15 13 15 33.
  Definition loc_132 : location_info := LocationInfo file_1 15 13 15 28.
  Definition loc_133 : location_info := LocationInfo file_1 14 8 14 9.
  Definition loc_136 : location_info := LocationInfo file_1 49 2 52 3.
  Definition loc_137 : location_info := LocationInfo file_1 54 2 54 34.
  Definition loc_138 : location_info := LocationInfo file_1 55 2 55 21.
  Definition loc_139 : location_info := LocationInfo file_1 57 2 57 33.
  Definition loc_140 : location_info := LocationInfo file_1 58 2 58 51.
  Definition loc_141 : location_info := LocationInfo file_1 58 51 58 3.
  Definition loc_142 : location_info := LocationInfo file_1 60 2 60 37.
  Definition loc_143 : location_info := LocationInfo file_1 61 2 61 31.
  Definition loc_144 : location_info := LocationInfo file_1 63 2 63 35.
  Definition loc_145 : location_info := LocationInfo file_1 63 2 63 11.
  Definition loc_146 : location_info := LocationInfo file_1 63 2 63 11.
  Definition loc_147 : location_info := LocationInfo file_1 63 12 63 33.
  Definition loc_148 : location_info := LocationInfo file_1 63 13 63 33.
  Definition loc_149 : location_info := LocationInfo file_1 63 13 63 28.
  Definition loc_150 : location_info := LocationInfo file_1 61 2 61 22.
  Definition loc_151 : location_info := LocationInfo file_1 61 2 61 17.
  Definition loc_152 : location_info := LocationInfo file_1 61 25 61 30.
  Definition loc_153 : location_info := LocationInfo file_1 61 25 61 30.
  Definition loc_154 : location_info := LocationInfo file_1 60 2 60 13.
  Definition loc_155 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_156 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_157 : location_info := LocationInfo file_1 60 16 60 36.
  Definition loc_158 : location_info := LocationInfo file_1 60 16 60 36.
  Definition loc_159 : location_info := LocationInfo file_1 60 16 60 31.
  Definition loc_160 : location_info := LocationInfo file_1 58 27 58 50.
  Definition loc_161 : location_info := LocationInfo file_1 58 28 58 50.
  Definition loc_162 : location_info := LocationInfo file_1 58 29 58 44.
  Definition loc_163 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_164 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_165 : location_info := LocationInfo file_1 57 10 57 31.
  Definition loc_166 : location_info := LocationInfo file_1 57 11 57 31.
  Definition loc_167 : location_info := LocationInfo file_1 57 11 57 26.
  Definition loc_168 : location_info := LocationInfo file_1 55 2 55 13.
  Definition loc_169 : location_info := LocationInfo file_1 55 2 55 7.
  Definition loc_170 : location_info := LocationInfo file_1 55 2 55 7.
  Definition loc_171 : location_info := LocationInfo file_1 55 16 55 20.
  Definition loc_172 : location_info := LocationInfo file_1 55 16 55 20.
  Definition loc_173 : location_info := LocationInfo file_1 54 30 54 33.
  Definition loc_174 : location_info := LocationInfo file_1 54 30 54 33.
  Definition loc_177 : location_info := LocationInfo file_1 49 41 52 3.
  Definition loc_178 : location_info := LocationInfo file_1 51 4 51 11.
  Definition loc_181 : location_info := LocationInfo file_1 49 6 49 39.
  Definition loc_182 : location_info := LocationInfo file_1 49 6 49 10.
  Definition loc_183 : location_info := LocationInfo file_1 49 6 49 10.
  Definition loc_184 : location_info := LocationInfo file_1 49 13 49 39.
  Definition loc_187 : location_info := LocationInfo file_1 79 2 79 25.
  Definition loc_188 : location_info := LocationInfo file_1 79 9 79 24.
  Definition loc_189 : location_info := LocationInfo file_1 79 9 79 14.
  Definition loc_190 : location_info := LocationInfo file_1 79 9 79 14.
  Definition loc_191 : location_info := LocationInfo file_1 79 15 79 23.
  Definition loc_192 : location_info := LocationInfo file_1 79 15 79 16.
  Definition loc_193 : location_info := LocationInfo file_1 79 15 79 16.
  Definition loc_194 : location_info := LocationInfo file_1 79 19 79 23.
  Definition loc_195 : location_info := LocationInfo file_1 79 19 79 23.
  Definition loc_198 : location_info := LocationInfo file_1 84 2 84 22.
  Definition loc_199 : location_info := LocationInfo file_1 84 2 84 6.
  Definition loc_200 : location_info := LocationInfo file_1 84 2 84 6.
  Definition loc_201 : location_info := LocationInfo file_1 84 7 84 15.
  Definition loc_202 : location_info := LocationInfo file_1 84 7 84 8.
  Definition loc_203 : location_info := LocationInfo file_1 84 7 84 8.
  Definition loc_204 : location_info := LocationInfo file_1 84 11 84 15.
  Definition loc_205 : location_info := LocationInfo file_1 84 11 84 15.
  Definition loc_206 : location_info := LocationInfo file_1 84 17 84 20.
  Definition loc_207 : location_info := LocationInfo file_1 84 17 84 20.
  Definition loc_210 : location_info := LocationInfo file_1 67 2 67 33.
  Definition loc_211 : location_info := LocationInfo file_1 68 2 68 40.
  Definition loc_212 : location_info := LocationInfo file_1 72 2 72 12.
  Definition loc_213 : location_info := LocationInfo file_1 72 12 72 13.
  Definition loc_214 : location_info := LocationInfo file_1 74 2 74 49.
  Definition loc_215 : location_info := LocationInfo file_1 74 49 74 3.
  Definition loc_216 : location_info := LocationInfo file_1 74 30 74 48.
  Definition loc_217 : location_info := LocationInfo file_1 74 31 74 48.
  Definition loc_218 : location_info := LocationInfo file_1 72 2 72 12.
  Definition loc_219 : location_info := LocationInfo file_1 72 10 72 12.
  Definition loc_220 : location_info := LocationInfo file_1 72 2 72 12.
  Definition loc_221 : location_info := LocationInfo file_1 72 2 72 12.
  Definition loc_222 : location_info := LocationInfo file_1 72 8 72 9.
  Definition loc_223 : location_info := LocationInfo file_1 68 2 68 22.
  Definition loc_224 : location_info := LocationInfo file_1 68 2 68 17.
  Definition loc_225 : location_info := LocationInfo file_1 68 25 68 39.
  Definition loc_226 : location_info := LocationInfo file_1 67 2 67 9.
  Definition loc_227 : location_info := LocationInfo file_1 67 2 67 9.
  Definition loc_228 : location_info := LocationInfo file_1 67 10 67 31.
  Definition loc_229 : location_info := LocationInfo file_1 67 11 67 31.
  Definition loc_230 : location_info := LocationInfo file_1 67 11 67 26.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{it_layout uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc]. *)
  Definition impl_alloc (global_allocator_state global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t)
    ];
    f_local_vars := [
      ("prev", void*);
      ("cur", void*);
      ("ret", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_133 ;
        if: LocInfoE loc_133 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_133 (i2v 1 i32)))
        then
        locinfo: loc_14 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_32 ;
        Goto "#8"
      ]> $
      <[ "#11" :=
        locinfo: loc_83 ;
        LocInfoE loc_94 (!{void*} (LocInfoE loc_95 ("prev"))) <-{ void* }
          LocInfoE loc_96 (use{void*} (LocInfoE loc_97 ((LocInfoE loc_98 (!{void*} (LocInfoE loc_99 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_84 ;
        expr: (LocInfoE loc_84 (Call (LocInfoE loc_89 (global_sl_unlock)) [@{expr} LocInfoE loc_90 (AnnotExpr 1%nat LockA (LocInfoE loc_90 (&(LocInfoE loc_91 ((LocInfoE loc_92 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_85 ;
        Return (LocInfoE loc_86 (use{void*} (LocInfoE loc_87 ("cur"))))
      ]> $
      <[ "#12" :=
        locinfo: loc_73 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_14 ;
        expr: (LocInfoE loc_14 (Call (LocInfoE loc_129 (global_sl_lock)) [@{expr} LocInfoE loc_130 (&(LocInfoE loc_131 ((LocInfoE loc_132 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_15 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_125 (&(LocInfoE loc_126 ((LocInfoE loc_127 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        "prev" <-{ void* }
          LocInfoE loc_120 (&(LocInfoE loc_121 ((LocInfoE loc_122 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_18 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_114 ;
        if: LocInfoE loc_114 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_114 ((LocInfoE loc_115 (use{void*} (LocInfoE loc_117 (!{void*} (LocInfoE loc_118 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_119 (NULL)))))
        then
        Goto "#5"
        else
        locinfo: loc_19 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        "cur" <-{ void* }
          LocInfoE loc_108 (use{void*} (LocInfoE loc_110 (!{void*} (LocInfoE loc_111 ("prev"))))) ;
        locinfo: loc_101 ;
        if: LocInfoE loc_101 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_101 ((LocInfoE loc_102 (use{it_layout size_t} (LocInfoE loc_103 ((LocInfoE loc_104 (!{void*} (LocInfoE loc_105 ("cur")))) at{struct_alloc_entry} "size")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_106 (use{it_layout size_t} (LocInfoE loc_107 ("size")))))))
        then
        locinfo: loc_83 ;
          Goto "#11"
        else
        locinfo: loc_73 ;
          Goto "#12"
      ]> $
      <[ "#6" :=
        locinfo: loc_19 ;
        expr: (LocInfoE loc_19 (Call (LocInfoE loc_23 (global_sl_unlock)) [@{expr} LocInfoE loc_24 (AnnotExpr 1%nat LockA (LocInfoE loc_24 (&(LocInfoE loc_25 ((LocInfoE loc_26 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_20 ;
        Goto "continue4"
      ]> $
      <[ "#7" :=
        locinfo: loc_73 ;
        if: LocInfoE loc_73 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_73 ((LocInfoE loc_74 (use{it_layout size_t} (LocInfoE loc_75 ((LocInfoE loc_76 (!{void*} (LocInfoE loc_77 ("cur")))) at{struct_alloc_entry} "size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_78 ((LocInfoE loc_79 (use{it_layout size_t} (LocInfoE loc_80 ("size")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_81 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))))
        then
        locinfo: loc_41 ;
          Goto "#9"
        else
        locinfo: loc_32 ;
          Goto "#10"
      ]> $
      <[ "#8" :=
        locinfo: loc_32 ;
        LocInfoE loc_35 ("prev") <-{ void* }
          LocInfoE loc_36 (&(LocInfoE loc_37 ((LocInfoE loc_38 (!{void*} (LocInfoE loc_39 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_33 ;
        Goto "continue6"
      ]> $
      <[ "#9" :=
        locinfo: loc_41 ;
        LocInfoE loc_62 ((LocInfoE loc_63 (!{void*} (LocInfoE loc_64 ("cur")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_65 ((LocInfoE loc_66 (use{it_layout size_t} (LocInfoE loc_67 ((LocInfoE loc_68 (!{void*} (LocInfoE loc_69 ("cur")))) at{struct_alloc_entry} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_70 (use{it_layout size_t} (LocInfoE loc_71 ("size"))))) ;
        "ret" <-{ void* }
          LocInfoE loc_52 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_52 ((LocInfoE loc_53 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_54 (use{void*} (LocInfoE loc_55 ("cur")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_56 (use{it_layout size_t} (LocInfoE loc_57 ((LocInfoE loc_58 (!{void*} (LocInfoE loc_59 ("cur")))) at{struct_alloc_entry} "size"))))))) ;
        locinfo: loc_43 ;
        expr: (LocInfoE loc_43 (Call (LocInfoE loc_48 (global_sl_unlock)) [@{expr} LocInfoE loc_49 (AnnotExpr 1%nat LockA (LocInfoE loc_49 (&(LocInfoE loc_50 ((LocInfoE loc_51 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_44 ;
        Return (LocInfoE loc_45 (use{void*} (LocInfoE loc_46 ("ret"))))
      ]> $
      <[ "continue4" :=
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "continue6" :=
        locinfo: loc_18 ;
        Goto "#4"
      ]> $∅
    )%E
  |}.

  (* Definition of function [free]. *)
  Definition impl_free (global_allocator_state global_sl_lock global_sl_unlock : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("ptr", void*)
    ];
    f_local_vars := [
      ("entry", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_181 ;
        if: LocInfoE loc_181 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_181 ((LocInfoE loc_182 (use{it_layout size_t} (LocInfoE loc_183 ("size")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_184 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))
        then
        locinfo: loc_178 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ void* }
          LocInfoE loc_173 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_173 (use{void*} (LocInfoE loc_174 ("ptr"))))) ;
        locinfo: loc_138 ;
        LocInfoE loc_168 ((LocInfoE loc_169 (!{void*} (LocInfoE loc_170 ("entry")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_171 (use{it_layout size_t} (LocInfoE loc_172 ("size"))) ;
        locinfo: loc_139 ;
        expr: (LocInfoE loc_139 (Call (LocInfoE loc_164 (global_sl_lock)) [@{expr} LocInfoE loc_165 (&(LocInfoE loc_166 ((LocInfoE loc_167 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_140 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_160 (&(LocInfoE loc_161 ((LocInfoE loc_162 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        locinfo: loc_142 ;
        LocInfoE loc_154 ((LocInfoE loc_155 (!{void*} (LocInfoE loc_156 ("entry")))) at{struct_alloc_entry} "next") <-{ void* }
          LocInfoE loc_157 (use{void*} (LocInfoE loc_158 ((LocInfoE loc_159 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_143 ;
        LocInfoE loc_150 ((LocInfoE loc_151 (global_allocator_state)) at{struct_alloc_state} "data") <-{ void* }
          LocInfoE loc_152 (use{void*} (LocInfoE loc_153 ("entry"))) ;
        locinfo: loc_144 ;
        expr: (LocInfoE loc_144 (Call (LocInfoE loc_146 (global_sl_unlock)) [@{expr} LocInfoE loc_147 (AnnotExpr 1%nat LockA (LocInfoE loc_147 (&(LocInfoE loc_148 ((LocInfoE loc_149 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_178 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [alloc_array]. *)
  Definition impl_alloc_array (global_alloc : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_187 ;
        Return (LocInfoE loc_188 (Call (LocInfoE loc_190 (global_alloc)) [@{expr} LocInfoE loc_191 ((LocInfoE loc_192 (use{it_layout size_t} (LocInfoE loc_193 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_194 (use{it_layout size_t} (LocInfoE loc_195 ("size"))))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [free_array]. *)
  Definition impl_free_array (global_free : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("n", it_layout size_t);
      ("ptr", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_198 ;
        expr: (LocInfoE loc_198 (Call (LocInfoE loc_200 (global_free)) [@{expr} LocInfoE loc_201 ((LocInfoE loc_202 (use{it_layout size_t} (LocInfoE loc_203 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_204 (use{it_layout size_t} (LocInfoE loc_205 ("size"))))) ;
        LocInfoE loc_206 (use{void*} (LocInfoE loc_207 ("ptr"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_alloc]. *)
  Definition impl_init_alloc (global_allocator_state global_sl_init : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_210 ;
        expr: (LocInfoE loc_210 (Call (LocInfoE loc_227 (global_sl_init)) [@{expr} LocInfoE loc_228 (&(LocInfoE loc_229 ((LocInfoE loc_230 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_211 ;
        LocInfoE loc_223 ((LocInfoE loc_224 (global_allocator_state)) at{struct_alloc_state} "data") <-{ void* }
          LocInfoE loc_225 (NULL) ;
        locinfo: loc_212 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_222 ;
        if: LocInfoE loc_222 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_222 (i2v 0 i32)))
        then
        locinfo: loc_220 ;
          Goto "#2"
        else
        locinfo: loc_214 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_220 ;
        Goto "continue15"
      ]> $
      <[ "#3" :=
        locinfo: loc_214 ;
        annot: (ShareAnnot) ;
        expr: (LocInfoE loc_216 (&(LocInfoE loc_217 (global_allocator_state)))) ;
        Return (VOID)
      ]> $
      <[ "continue15" :=
        locinfo: loc_212 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
