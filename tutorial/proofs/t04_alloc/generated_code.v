From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t04_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 14 2 43 3.
  Definition loc_12 : location_info := LocationInfo file_1 14 11 43 3.
  Definition loc_13 : location_info := LocationInfo file_1 15 4 15 35.
  Definition loc_14 : location_info := LocationInfo file_1 16 4 16 53.
  Definition loc_15 : location_info := LocationInfo file_1 16 53 16 5.
  Definition loc_16 : location_info := LocationInfo file_1 19 4 19 48.
  Definition loc_17 : location_info := LocationInfo file_1 24 4 40 5.
  Definition loc_18 : location_info := LocationInfo file_1 42 4 42 37.
  Definition loc_19 : location_info := LocationInfo file_1 42 4 42 13.
  Definition loc_20 : location_info := LocationInfo file_1 42 4 42 13.
  Definition loc_21 : location_info := LocationInfo file_1 42 14 42 35.
  Definition loc_22 : location_info := LocationInfo file_1 42 15 42 35.
  Definition loc_23 : location_info := LocationInfo file_1 42 15 42 30.
  Definition loc_24 : location_info := LocationInfo file_1 24 35 40 5.
  Definition loc_25 : location_info := LocationInfo file_1 25 6 25 32.
  Definition loc_26 : location_info := LocationInfo file_1 27 6 31 7.
  Definition loc_27 : location_info := LocationInfo file_1 32 6 37 7.
  Definition loc_28 : location_info := LocationInfo file_1 39 6 39 24.
  Definition loc_29 : location_info := LocationInfo file_1 39 6 39 10.
  Definition loc_30 : location_info := LocationInfo file_1 39 13 39 23.
  Definition loc_31 : location_info := LocationInfo file_1 39 14 39 23.
  Definition loc_32 : location_info := LocationInfo file_1 39 14 39 17.
  Definition loc_33 : location_info := LocationInfo file_1 39 14 39 17.
  Definition loc_34 : location_info := LocationInfo file_1 32 57 37 7.
  Definition loc_35 : location_info := LocationInfo file_1 33 8 33 26.
  Definition loc_36 : location_info := LocationInfo file_1 34 8 34 54.
  Definition loc_37 : location_info := LocationInfo file_1 35 8 35 41.
  Definition loc_38 : location_info := LocationInfo file_1 36 8 36 19.
  Definition loc_39 : location_info := LocationInfo file_1 36 15 36 18.
  Definition loc_40 : location_info := LocationInfo file_1 36 15 36 18.
  Definition loc_41 : location_info := LocationInfo file_1 35 8 35 17.
  Definition loc_42 : location_info := LocationInfo file_1 35 8 35 17.
  Definition loc_43 : location_info := LocationInfo file_1 35 18 35 39.
  Definition loc_44 : location_info := LocationInfo file_1 35 19 35 39.
  Definition loc_45 : location_info := LocationInfo file_1 35 19 35 34.
  Definition loc_46 : location_info := LocationInfo file_1 34 20 34 53.
  Definition loc_47 : location_info := LocationInfo file_1 34 21 34 40.
  Definition loc_48 : location_info := LocationInfo file_1 34 37 34 40.
  Definition loc_49 : location_info := LocationInfo file_1 34 37 34 40.
  Definition loc_50 : location_info := LocationInfo file_1 34 43 34 52.
  Definition loc_51 : location_info := LocationInfo file_1 34 43 34 52.
  Definition loc_52 : location_info := LocationInfo file_1 34 43 34 46.
  Definition loc_53 : location_info := LocationInfo file_1 34 43 34 46.
  Definition loc_56 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_57 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_58 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_59 : location_info := LocationInfo file_1 33 8 33 25.
  Definition loc_60 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_61 : location_info := LocationInfo file_1 33 8 33 17.
  Definition loc_62 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_63 : location_info := LocationInfo file_1 33 8 33 11.
  Definition loc_64 : location_info := LocationInfo file_1 33 21 33 25.
  Definition loc_65 : location_info := LocationInfo file_1 33 21 33 25.
  Definition loc_66 : location_info := LocationInfo file_1 32 6 37 7.
  Definition loc_67 : location_info := LocationInfo file_1 32 9 32 55.
  Definition loc_68 : location_info := LocationInfo file_1 32 9 32 18.
  Definition loc_69 : location_info := LocationInfo file_1 32 9 32 18.
  Definition loc_70 : location_info := LocationInfo file_1 32 9 32 12.
  Definition loc_71 : location_info := LocationInfo file_1 32 9 32 12.
  Definition loc_72 : location_info := LocationInfo file_1 32 22 32 55.
  Definition loc_73 : location_info := LocationInfo file_1 32 22 32 26.
  Definition loc_74 : location_info := LocationInfo file_1 32 22 32 26.
  Definition loc_75 : location_info := LocationInfo file_1 32 29 32 55.
  Definition loc_76 : location_info := LocationInfo file_1 27 28 31 7.
  Definition loc_77 : location_info := LocationInfo file_1 28 8 28 26.
  Definition loc_78 : location_info := LocationInfo file_1 29 8 29 41.
  Definition loc_79 : location_info := LocationInfo file_1 30 8 30 19.
  Definition loc_80 : location_info := LocationInfo file_1 30 15 30 18.
  Definition loc_81 : location_info := LocationInfo file_1 30 15 30 18.
  Definition loc_82 : location_info := LocationInfo file_1 29 8 29 17.
  Definition loc_83 : location_info := LocationInfo file_1 29 8 29 17.
  Definition loc_84 : location_info := LocationInfo file_1 29 18 29 39.
  Definition loc_85 : location_info := LocationInfo file_1 29 19 29 39.
  Definition loc_86 : location_info := LocationInfo file_1 29 19 29 34.
  Definition loc_87 : location_info := LocationInfo file_1 28 8 28 13.
  Definition loc_88 : location_info := LocationInfo file_1 28 9 28 13.
  Definition loc_89 : location_info := LocationInfo file_1 28 9 28 13.
  Definition loc_90 : location_info := LocationInfo file_1 28 16 28 25.
  Definition loc_91 : location_info := LocationInfo file_1 28 16 28 25.
  Definition loc_92 : location_info := LocationInfo file_1 28 16 28 19.
  Definition loc_93 : location_info := LocationInfo file_1 28 16 28 19.
  Definition loc_94 : location_info := LocationInfo file_1 27 6 31 7.
  Definition loc_95 : location_info := LocationInfo file_1 27 9 27 26.
  Definition loc_96 : location_info := LocationInfo file_1 27 9 27 18.
  Definition loc_97 : location_info := LocationInfo file_1 27 9 27 18.
  Definition loc_98 : location_info := LocationInfo file_1 27 9 27 12.
  Definition loc_99 : location_info := LocationInfo file_1 27 9 27 12.
  Definition loc_100 : location_info := LocationInfo file_1 27 22 27 26.
  Definition loc_101 : location_info := LocationInfo file_1 27 22 27 26.
  Definition loc_102 : location_info := LocationInfo file_1 25 26 25 31.
  Definition loc_103 : location_info := LocationInfo file_1 25 26 25 31.
  Definition loc_104 : location_info := LocationInfo file_1 25 27 25 31.
  Definition loc_105 : location_info := LocationInfo file_1 25 27 25 31.
  Definition loc_108 : location_info := LocationInfo file_1 24 10 24 33.
  Definition loc_109 : location_info := LocationInfo file_1 24 10 24 15.
  Definition loc_110 : location_info := LocationInfo file_1 24 10 24 15.
  Definition loc_111 : location_info := LocationInfo file_1 24 11 24 15.
  Definition loc_112 : location_info := LocationInfo file_1 24 11 24 15.
  Definition loc_113 : location_info := LocationInfo file_1 24 19 24 33.
  Definition loc_114 : location_info := LocationInfo file_1 19 26 19 47.
  Definition loc_115 : location_info := LocationInfo file_1 19 27 19 47.
  Definition loc_116 : location_info := LocationInfo file_1 19 27 19 42.
  Definition loc_119 : location_info := LocationInfo file_1 16 29 16 52.
  Definition loc_120 : location_info := LocationInfo file_1 16 30 16 52.
  Definition loc_121 : location_info := LocationInfo file_1 16 31 16 46.
  Definition loc_122 : location_info := LocationInfo file_1 15 4 15 11.
  Definition loc_123 : location_info := LocationInfo file_1 15 4 15 11.
  Definition loc_124 : location_info := LocationInfo file_1 15 12 15 33.
  Definition loc_125 : location_info := LocationInfo file_1 15 13 15 33.
  Definition loc_126 : location_info := LocationInfo file_1 15 13 15 28.
  Definition loc_127 : location_info := LocationInfo file_1 14 8 14 9.
  Definition loc_130 : location_info := LocationInfo file_1 49 2 52 3.
  Definition loc_131 : location_info := LocationInfo file_1 54 2 54 34.
  Definition loc_132 : location_info := LocationInfo file_1 55 2 55 21.
  Definition loc_133 : location_info := LocationInfo file_1 57 2 57 33.
  Definition loc_134 : location_info := LocationInfo file_1 58 2 58 51.
  Definition loc_135 : location_info := LocationInfo file_1 58 51 58 3.
  Definition loc_136 : location_info := LocationInfo file_1 60 2 60 37.
  Definition loc_137 : location_info := LocationInfo file_1 61 2 61 31.
  Definition loc_138 : location_info := LocationInfo file_1 63 2 63 35.
  Definition loc_139 : location_info := LocationInfo file_1 63 2 63 11.
  Definition loc_140 : location_info := LocationInfo file_1 63 2 63 11.
  Definition loc_141 : location_info := LocationInfo file_1 63 12 63 33.
  Definition loc_142 : location_info := LocationInfo file_1 63 13 63 33.
  Definition loc_143 : location_info := LocationInfo file_1 63 13 63 28.
  Definition loc_144 : location_info := LocationInfo file_1 61 2 61 22.
  Definition loc_145 : location_info := LocationInfo file_1 61 2 61 17.
  Definition loc_146 : location_info := LocationInfo file_1 61 25 61 30.
  Definition loc_147 : location_info := LocationInfo file_1 61 25 61 30.
  Definition loc_148 : location_info := LocationInfo file_1 60 2 60 13.
  Definition loc_149 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_150 : location_info := LocationInfo file_1 60 2 60 7.
  Definition loc_151 : location_info := LocationInfo file_1 60 16 60 36.
  Definition loc_152 : location_info := LocationInfo file_1 60 16 60 36.
  Definition loc_153 : location_info := LocationInfo file_1 60 16 60 31.
  Definition loc_154 : location_info := LocationInfo file_1 58 27 58 50.
  Definition loc_155 : location_info := LocationInfo file_1 58 28 58 50.
  Definition loc_156 : location_info := LocationInfo file_1 58 29 58 44.
  Definition loc_157 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_158 : location_info := LocationInfo file_1 57 2 57 9.
  Definition loc_159 : location_info := LocationInfo file_1 57 10 57 31.
  Definition loc_160 : location_info := LocationInfo file_1 57 11 57 31.
  Definition loc_161 : location_info := LocationInfo file_1 57 11 57 26.
  Definition loc_162 : location_info := LocationInfo file_1 55 2 55 13.
  Definition loc_163 : location_info := LocationInfo file_1 55 2 55 7.
  Definition loc_164 : location_info := LocationInfo file_1 55 2 55 7.
  Definition loc_165 : location_info := LocationInfo file_1 55 16 55 20.
  Definition loc_166 : location_info := LocationInfo file_1 55 16 55 20.
  Definition loc_167 : location_info := LocationInfo file_1 54 30 54 33.
  Definition loc_168 : location_info := LocationInfo file_1 54 30 54 33.
  Definition loc_171 : location_info := LocationInfo file_1 49 41 52 3.
  Definition loc_172 : location_info := LocationInfo file_1 51 4 51 11.
  Definition loc_174 : location_info := LocationInfo file_1 49 2 52 3.
  Definition loc_175 : location_info := LocationInfo file_1 49 6 49 39.
  Definition loc_176 : location_info := LocationInfo file_1 49 6 49 10.
  Definition loc_177 : location_info := LocationInfo file_1 49 6 49 10.
  Definition loc_178 : location_info := LocationInfo file_1 49 13 49 39.
  Definition loc_181 : location_info := LocationInfo file_1 78 2 78 26.
  Definition loc_182 : location_info := LocationInfo file_1 78 9 78 25.
  Definition loc_183 : location_info := LocationInfo file_1 78 9 78 15.
  Definition loc_184 : location_info := LocationInfo file_1 78 9 78 15.
  Definition loc_185 : location_info := LocationInfo file_1 78 16 78 24.
  Definition loc_186 : location_info := LocationInfo file_1 78 16 78 17.
  Definition loc_187 : location_info := LocationInfo file_1 78 16 78 17.
  Definition loc_188 : location_info := LocationInfo file_1 78 20 78 24.
  Definition loc_189 : location_info := LocationInfo file_1 78 20 78 24.
  Definition loc_192 : location_info := LocationInfo file_1 83 2 83 23.
  Definition loc_193 : location_info := LocationInfo file_1 83 2 83 7.
  Definition loc_194 : location_info := LocationInfo file_1 83 2 83 7.
  Definition loc_195 : location_info := LocationInfo file_1 83 8 83 16.
  Definition loc_196 : location_info := LocationInfo file_1 83 8 83 9.
  Definition loc_197 : location_info := LocationInfo file_1 83 8 83 9.
  Definition loc_198 : location_info := LocationInfo file_1 83 12 83 16.
  Definition loc_199 : location_info := LocationInfo file_1 83 12 83 16.
  Definition loc_200 : location_info := LocationInfo file_1 83 18 83 21.
  Definition loc_201 : location_info := LocationInfo file_1 83 18 83 21.
  Definition loc_204 : location_info := LocationInfo file_1 67 2 67 33.
  Definition loc_205 : location_info := LocationInfo file_1 68 2 68 40.
  Definition loc_206 : location_info := LocationInfo file_1 70 2 71 17.
  Definition loc_207 : location_info := LocationInfo file_1 71 17 71 3.
  Definition loc_208 : location_info := LocationInfo file_1 73 2 73 49.
  Definition loc_209 : location_info := LocationInfo file_1 73 49 73 3.
  Definition loc_210 : location_info := LocationInfo file_1 73 30 73 48.
  Definition loc_211 : location_info := LocationInfo file_1 73 31 73 48.
  Definition loc_212 : location_info := LocationInfo file_1 71 15 71 16.
  Definition loc_213 : location_info := LocationInfo file_1 68 2 68 22.
  Definition loc_214 : location_info := LocationInfo file_1 68 2 68 17.
  Definition loc_215 : location_info := LocationInfo file_1 68 25 68 39.
  Definition loc_216 : location_info := LocationInfo file_1 67 2 67 9.
  Definition loc_217 : location_info := LocationInfo file_1 67 2 67 9.
  Definition loc_218 : location_info := LocationInfo file_1 67 10 67 31.
  Definition loc_219 : location_info := LocationInfo file_1 67 11 67 31.
  Definition loc_220 : location_info := LocationInfo file_1 67 11 67 26.

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
        Return (LocInfoE loc_3 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_5 (use{IntOp uintptr_t} (LocInfoE loc_6 ("to")))) (LocInfoE loc_7 (use{PtrOp} (LocInfoE loc_8 ("from"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [talloc]. *)
  Definition impl_talloc (global_allocator_state global_sl_lock global_sl_unlock : loc): function := {|
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
        locinfo: loc_127 ;
        if{IntOp i32, None}: LocInfoE loc_127 (i2v 1 i32)
        then
        locinfo: loc_13 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_28 ;
        Goto "#8"
      ]> $
      <[ "#11" :=
        locinfo: loc_77 ;
        LocInfoE loc_88 (!{PtrOp} (LocInfoE loc_89 ("prev"))) <-{ PtrOp }
          LocInfoE loc_90 (use{PtrOp} (LocInfoE loc_91 ((LocInfoE loc_92 (!{PtrOp} (LocInfoE loc_93 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_78 ;
        expr: (LocInfoE loc_78 (Call (LocInfoE loc_83 (global_sl_unlock)) [@{expr} LocInfoE loc_84 (AnnotExpr 1%nat LockA (LocInfoE loc_84 (&(LocInfoE loc_85 ((LocInfoE loc_86 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_79 ;
        Return (LocInfoE loc_80 (use{PtrOp} (LocInfoE loc_81 ("cur"))))
      ]> $
      <[ "#12" :=
        locinfo: loc_67 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_13 ;
        expr: (LocInfoE loc_13 (Call (LocInfoE loc_123 (global_sl_lock)) [@{expr} LocInfoE loc_124 (&(LocInfoE loc_125 ((LocInfoE loc_126 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_14 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_119 (&(LocInfoE loc_120 ((LocInfoE loc_121 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        "prev" <-{ PtrOp }
          LocInfoE loc_114 (&(LocInfoE loc_115 ((LocInfoE loc_116 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_17 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_108 ;
        if{IntOp i32, None}: LocInfoE loc_108 ((LocInfoE loc_109 (use{PtrOp} (LocInfoE loc_111 (!{PtrOp} (LocInfoE loc_112 ("prev")))))) !={PtrOp, PtrOp, i32} (LocInfoE loc_113 (NULL)))
        then
        Goto "#5"
        else
        locinfo: loc_18 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        "cur" <-{ PtrOp }
          LocInfoE loc_102 (use{PtrOp} (LocInfoE loc_104 (!{PtrOp} (LocInfoE loc_105 ("prev"))))) ;
        locinfo: loc_95 ;
        if{IntOp i32, Some "#7"}: LocInfoE loc_95 ((LocInfoE loc_96 (use{IntOp size_t} (LocInfoE loc_97 ((LocInfoE loc_98 (!{PtrOp} (LocInfoE loc_99 ("cur")))) at{struct_alloc_entry} "size")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_100 (use{IntOp size_t} (LocInfoE loc_101 ("size")))))
        then
        locinfo: loc_77 ;
          Goto "#11"
        else
        locinfo: loc_67 ;
          Goto "#12"
      ]> $
      <[ "#6" :=
        locinfo: loc_18 ;
        expr: (LocInfoE loc_18 (Call (LocInfoE loc_20 (global_sl_unlock)) [@{expr} LocInfoE loc_21 (AnnotExpr 1%nat LockA (LocInfoE loc_21 (&(LocInfoE loc_22 ((LocInfoE loc_23 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_11 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_67 ;
        if{IntOp i32, Some "#8"}: LocInfoE loc_67 ((LocInfoE loc_68 (use{IntOp size_t} (LocInfoE loc_69 ((LocInfoE loc_70 (!{PtrOp} (LocInfoE loc_71 ("cur")))) at{struct_alloc_entry} "size")))) ≥{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_72 ((LocInfoE loc_73 (use{IntOp size_t} (LocInfoE loc_74 ("size")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_75 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))
        then
        locinfo: loc_35 ;
          Goto "#9"
        else
        locinfo: loc_28 ;
          Goto "#10"
      ]> $
      <[ "#8" :=
        locinfo: loc_28 ;
        LocInfoE loc_29 ("prev") <-{ PtrOp }
          LocInfoE loc_30 (&(LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_17 ;
        Goto "#4"
      ]> $
      <[ "#9" :=
        locinfo: loc_35 ;
        LocInfoE loc_56 ((LocInfoE loc_57 (!{PtrOp} (LocInfoE loc_58 ("cur")))) at{struct_alloc_entry} "size") <-{ IntOp size_t }
          LocInfoE loc_59 ((LocInfoE loc_60 (use{IntOp size_t} (LocInfoE loc_61 ((LocInfoE loc_62 (!{PtrOp} (LocInfoE loc_63 ("cur")))) at{struct_alloc_entry} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_64 (use{IntOp size_t} (LocInfoE loc_65 ("size"))))) ;
        "ret" <-{ PtrOp }
          LocInfoE loc_46 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_46 ((LocInfoE loc_47 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_48 (use{PtrOp} (LocInfoE loc_49 ("cur")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_50 (use{IntOp size_t} (LocInfoE loc_51 ((LocInfoE loc_52 (!{PtrOp} (LocInfoE loc_53 ("cur")))) at{struct_alloc_entry} "size"))))))) ;
        locinfo: loc_37 ;
        expr: (LocInfoE loc_37 (Call (LocInfoE loc_42 (global_sl_unlock)) [@{expr} LocInfoE loc_43 (AnnotExpr 1%nat LockA (LocInfoE loc_43 (&(LocInfoE loc_44 ((LocInfoE loc_45 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_38 ;
        Return (LocInfoE loc_39 (use{PtrOp} (LocInfoE loc_40 ("ret"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [tfree]. *)
  Definition impl_tfree (global_allocator_state global_sl_lock global_sl_unlock : loc): function := {|
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
        locinfo: loc_175 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_175 ((LocInfoE loc_176 (use{IntOp size_t} (LocInfoE loc_177 ("size")))) <{IntOp size_t, IntOp size_t, i32} (LocInfoE loc_178 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))
        then
        locinfo: loc_172 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ PtrOp }
          LocInfoE loc_167 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_167 (use{PtrOp} (LocInfoE loc_168 ("ptr"))))) ;
        locinfo: loc_132 ;
        LocInfoE loc_162 ((LocInfoE loc_163 (!{PtrOp} (LocInfoE loc_164 ("entry")))) at{struct_alloc_entry} "size") <-{ IntOp size_t }
          LocInfoE loc_165 (use{IntOp size_t} (LocInfoE loc_166 ("size"))) ;
        locinfo: loc_133 ;
        expr: (LocInfoE loc_133 (Call (LocInfoE loc_158 (global_sl_lock)) [@{expr} LocInfoE loc_159 (&(LocInfoE loc_160 ((LocInfoE loc_161 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_134 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_154 (&(LocInfoE loc_155 ((LocInfoE loc_156 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        locinfo: loc_136 ;
        LocInfoE loc_148 ((LocInfoE loc_149 (!{PtrOp} (LocInfoE loc_150 ("entry")))) at{struct_alloc_entry} "next") <-{ PtrOp }
          LocInfoE loc_151 (use{PtrOp} (LocInfoE loc_152 ((LocInfoE loc_153 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_137 ;
        LocInfoE loc_144 ((LocInfoE loc_145 (global_allocator_state)) at{struct_alloc_state} "data") <-{ PtrOp }
          LocInfoE loc_146 (use{PtrOp} (LocInfoE loc_147 ("entry"))) ;
        locinfo: loc_138 ;
        expr: (LocInfoE loc_138 (Call (LocInfoE loc_140 (global_sl_unlock)) [@{expr} LocInfoE loc_141 (AnnotExpr 1%nat LockA (LocInfoE loc_141 (&(LocInfoE loc_142 ((LocInfoE loc_143 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_172 ;
        Return (VOID)
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [talloc_array]. *)
  Definition impl_talloc_array (global_talloc : loc): function := {|
    f_args := [
      ("size", it_layout size_t);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_181 ;
        Return (LocInfoE loc_182 (Call (LocInfoE loc_184 (global_talloc)) [@{expr} LocInfoE loc_185 ((LocInfoE loc_186 (use{IntOp size_t} (LocInfoE loc_187 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_188 (use{IntOp size_t} (LocInfoE loc_189 ("size"))))) ]))
      ]> $∅
    )%E
  |}.

  (* Definition of function [tfree_array]. *)
  Definition impl_tfree_array (global_tfree : loc): function := {|
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
        locinfo: loc_192 ;
        expr: (LocInfoE loc_192 (Call (LocInfoE loc_194 (global_tfree)) [@{expr} LocInfoE loc_195 ((LocInfoE loc_196 (use{IntOp size_t} (LocInfoE loc_197 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_198 (use{IntOp size_t} (LocInfoE loc_199 ("size"))))) ;
        LocInfoE loc_200 (use{PtrOp} (LocInfoE loc_201 ("ptr"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [init_talloc]. *)
  Definition impl_init_talloc (global_allocator_state global_sl_init : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_204 ;
        expr: (LocInfoE loc_204 (Call (LocInfoE loc_217 (global_sl_init)) [@{expr} LocInfoE loc_218 (&(LocInfoE loc_219 ((LocInfoE loc_220 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_205 ;
        LocInfoE loc_213 ((LocInfoE loc_214 (global_allocator_state)) at{struct_alloc_state} "data") <-{ PtrOp }
          LocInfoE loc_215 (NULL) ;
        locinfo: loc_206 ;
        annot: (AssertAnnot "0") ;
        expr: (LocInfoE loc_212 (i2v 0 i32)) ;
        locinfo: loc_208 ;
        annot: (ShareAnnot) ;
        expr: (LocInfoE loc_210 (&(LocInfoE loc_211 (global_allocator_state)))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
