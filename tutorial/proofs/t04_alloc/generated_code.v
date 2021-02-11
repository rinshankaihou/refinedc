From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t04_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 14 2 43 3.
  Definition loc_3 : location_info := LocationInfo file_0 14 2 43 3.
  Definition loc_4 : location_info := LocationInfo file_0 14 11 43 3.
  Definition loc_5 : location_info := LocationInfo file_0 15 4 15 35.
  Definition loc_6 : location_info := LocationInfo file_0 16 4 16 53.
  Definition loc_7 : location_info := LocationInfo file_0 16 53 16 5.
  Definition loc_8 : location_info := LocationInfo file_0 19 4 19 48.
  Definition loc_9 : location_info := LocationInfo file_0 24 4 40 5.
  Definition loc_10 : location_info := LocationInfo file_0 42 4 42 37.
  Definition loc_11 : location_info := LocationInfo file_0 14 2 43 3.
  Definition loc_12 : location_info := LocationInfo file_0 14 2 43 3.
  Definition loc_13 : location_info := LocationInfo file_0 42 4 42 13.
  Definition loc_14 : location_info := LocationInfo file_0 42 4 42 13.
  Definition loc_15 : location_info := LocationInfo file_0 42 14 42 35.
  Definition loc_16 : location_info := LocationInfo file_0 42 15 42 35.
  Definition loc_17 : location_info := LocationInfo file_0 42 15 42 30.
  Definition loc_18 : location_info := LocationInfo file_0 24 4 40 5.
  Definition loc_19 : location_info := LocationInfo file_0 24 35 40 5.
  Definition loc_20 : location_info := LocationInfo file_0 25 6 25 32.
  Definition loc_21 : location_info := LocationInfo file_0 27 6 31 7.
  Definition loc_22 : location_info := LocationInfo file_0 32 6 37 7.
  Definition loc_23 : location_info := LocationInfo file_0 39 6 39 24.
  Definition loc_24 : location_info := LocationInfo file_0 24 4 40 5.
  Definition loc_25 : location_info := LocationInfo file_0 24 4 40 5.
  Definition loc_26 : location_info := LocationInfo file_0 39 6 39 10.
  Definition loc_27 : location_info := LocationInfo file_0 39 13 39 23.
  Definition loc_28 : location_info := LocationInfo file_0 39 14 39 23.
  Definition loc_29 : location_info := LocationInfo file_0 39 14 39 17.
  Definition loc_30 : location_info := LocationInfo file_0 39 14 39 17.
  Definition loc_31 : location_info := LocationInfo file_0 32 57 37 7.
  Definition loc_32 : location_info := LocationInfo file_0 33 8 33 26.
  Definition loc_33 : location_info := LocationInfo file_0 34 8 34 54.
  Definition loc_34 : location_info := LocationInfo file_0 35 8 35 41.
  Definition loc_35 : location_info := LocationInfo file_0 36 8 36 19.
  Definition loc_36 : location_info := LocationInfo file_0 36 15 36 18.
  Definition loc_37 : location_info := LocationInfo file_0 36 15 36 18.
  Definition loc_38 : location_info := LocationInfo file_0 35 8 35 17.
  Definition loc_39 : location_info := LocationInfo file_0 35 8 35 17.
  Definition loc_40 : location_info := LocationInfo file_0 35 18 35 39.
  Definition loc_41 : location_info := LocationInfo file_0 35 19 35 39.
  Definition loc_42 : location_info := LocationInfo file_0 35 19 35 34.
  Definition loc_43 : location_info := LocationInfo file_0 34 20 34 53.
  Definition loc_44 : location_info := LocationInfo file_0 34 21 34 40.
  Definition loc_45 : location_info := LocationInfo file_0 34 37 34 40.
  Definition loc_46 : location_info := LocationInfo file_0 34 37 34 40.
  Definition loc_47 : location_info := LocationInfo file_0 34 43 34 52.
  Definition loc_48 : location_info := LocationInfo file_0 34 43 34 52.
  Definition loc_49 : location_info := LocationInfo file_0 34 43 34 46.
  Definition loc_50 : location_info := LocationInfo file_0 34 43 34 46.
  Definition loc_53 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_54 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_55 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_56 : location_info := LocationInfo file_0 33 8 33 25.
  Definition loc_57 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_58 : location_info := LocationInfo file_0 33 8 33 17.
  Definition loc_59 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_60 : location_info := LocationInfo file_0 33 8 33 11.
  Definition loc_61 : location_info := LocationInfo file_0 33 21 33 25.
  Definition loc_62 : location_info := LocationInfo file_0 33 21 33 25.
  Definition loc_64 : location_info := LocationInfo file_0 32 9 32 55.
  Definition loc_65 : location_info := LocationInfo file_0 32 9 32 18.
  Definition loc_66 : location_info := LocationInfo file_0 32 9 32 18.
  Definition loc_67 : location_info := LocationInfo file_0 32 9 32 12.
  Definition loc_68 : location_info := LocationInfo file_0 32 9 32 12.
  Definition loc_69 : location_info := LocationInfo file_0 32 22 32 55.
  Definition loc_70 : location_info := LocationInfo file_0 32 22 32 26.
  Definition loc_71 : location_info := LocationInfo file_0 32 22 32 26.
  Definition loc_72 : location_info := LocationInfo file_0 32 29 32 55.
  Definition loc_73 : location_info := LocationInfo file_0 27 28 31 7.
  Definition loc_74 : location_info := LocationInfo file_0 28 8 28 26.
  Definition loc_75 : location_info := LocationInfo file_0 29 8 29 41.
  Definition loc_76 : location_info := LocationInfo file_0 30 8 30 19.
  Definition loc_77 : location_info := LocationInfo file_0 30 15 30 18.
  Definition loc_78 : location_info := LocationInfo file_0 30 15 30 18.
  Definition loc_79 : location_info := LocationInfo file_0 29 8 29 17.
  Definition loc_80 : location_info := LocationInfo file_0 29 8 29 17.
  Definition loc_81 : location_info := LocationInfo file_0 29 18 29 39.
  Definition loc_82 : location_info := LocationInfo file_0 29 19 29 39.
  Definition loc_83 : location_info := LocationInfo file_0 29 19 29 34.
  Definition loc_84 : location_info := LocationInfo file_0 28 8 28 13.
  Definition loc_85 : location_info := LocationInfo file_0 28 9 28 13.
  Definition loc_86 : location_info := LocationInfo file_0 28 9 28 13.
  Definition loc_87 : location_info := LocationInfo file_0 28 16 28 25.
  Definition loc_88 : location_info := LocationInfo file_0 28 16 28 25.
  Definition loc_89 : location_info := LocationInfo file_0 28 16 28 19.
  Definition loc_90 : location_info := LocationInfo file_0 28 16 28 19.
  Definition loc_92 : location_info := LocationInfo file_0 27 9 27 26.
  Definition loc_93 : location_info := LocationInfo file_0 27 9 27 18.
  Definition loc_94 : location_info := LocationInfo file_0 27 9 27 18.
  Definition loc_95 : location_info := LocationInfo file_0 27 9 27 12.
  Definition loc_96 : location_info := LocationInfo file_0 27 9 27 12.
  Definition loc_97 : location_info := LocationInfo file_0 27 22 27 26.
  Definition loc_98 : location_info := LocationInfo file_0 27 22 27 26.
  Definition loc_99 : location_info := LocationInfo file_0 25 26 25 31.
  Definition loc_100 : location_info := LocationInfo file_0 25 26 25 31.
  Definition loc_101 : location_info := LocationInfo file_0 25 27 25 31.
  Definition loc_102 : location_info := LocationInfo file_0 25 27 25 31.
  Definition loc_105 : location_info := LocationInfo file_0 24 10 24 33.
  Definition loc_106 : location_info := LocationInfo file_0 24 10 24 15.
  Definition loc_107 : location_info := LocationInfo file_0 24 10 24 15.
  Definition loc_108 : location_info := LocationInfo file_0 24 11 24 15.
  Definition loc_109 : location_info := LocationInfo file_0 24 11 24 15.
  Definition loc_110 : location_info := LocationInfo file_0 24 19 24 33.
  Definition loc_111 : location_info := LocationInfo file_0 19 26 19 47.
  Definition loc_112 : location_info := LocationInfo file_0 19 27 19 47.
  Definition loc_113 : location_info := LocationInfo file_0 19 27 19 42.
  Definition loc_116 : location_info := LocationInfo file_0 16 29 16 52.
  Definition loc_117 : location_info := LocationInfo file_0 16 30 16 52.
  Definition loc_118 : location_info := LocationInfo file_0 16 31 16 46.
  Definition loc_119 : location_info := LocationInfo file_0 15 4 15 11.
  Definition loc_120 : location_info := LocationInfo file_0 15 4 15 11.
  Definition loc_121 : location_info := LocationInfo file_0 15 12 15 33.
  Definition loc_122 : location_info := LocationInfo file_0 15 13 15 33.
  Definition loc_123 : location_info := LocationInfo file_0 15 13 15 28.
  Definition loc_124 : location_info := LocationInfo file_0 14 8 14 9.
  Definition loc_127 : location_info := LocationInfo file_0 49 2 52 3.
  Definition loc_128 : location_info := LocationInfo file_0 54 2 54 34.
  Definition loc_129 : location_info := LocationInfo file_0 55 2 55 21.
  Definition loc_130 : location_info := LocationInfo file_0 57 2 57 33.
  Definition loc_131 : location_info := LocationInfo file_0 58 2 58 51.
  Definition loc_132 : location_info := LocationInfo file_0 58 51 58 3.
  Definition loc_133 : location_info := LocationInfo file_0 60 2 60 37.
  Definition loc_134 : location_info := LocationInfo file_0 61 2 61 31.
  Definition loc_135 : location_info := LocationInfo file_0 63 2 63 35.
  Definition loc_136 : location_info := LocationInfo file_0 63 2 63 11.
  Definition loc_137 : location_info := LocationInfo file_0 63 2 63 11.
  Definition loc_138 : location_info := LocationInfo file_0 63 12 63 33.
  Definition loc_139 : location_info := LocationInfo file_0 63 13 63 33.
  Definition loc_140 : location_info := LocationInfo file_0 63 13 63 28.
  Definition loc_141 : location_info := LocationInfo file_0 61 2 61 22.
  Definition loc_142 : location_info := LocationInfo file_0 61 2 61 17.
  Definition loc_143 : location_info := LocationInfo file_0 61 25 61 30.
  Definition loc_144 : location_info := LocationInfo file_0 61 25 61 30.
  Definition loc_145 : location_info := LocationInfo file_0 60 2 60 13.
  Definition loc_146 : location_info := LocationInfo file_0 60 2 60 7.
  Definition loc_147 : location_info := LocationInfo file_0 60 2 60 7.
  Definition loc_148 : location_info := LocationInfo file_0 60 16 60 36.
  Definition loc_149 : location_info := LocationInfo file_0 60 16 60 36.
  Definition loc_150 : location_info := LocationInfo file_0 60 16 60 31.
  Definition loc_151 : location_info := LocationInfo file_0 58 27 58 50.
  Definition loc_152 : location_info := LocationInfo file_0 58 28 58 50.
  Definition loc_153 : location_info := LocationInfo file_0 58 29 58 44.
  Definition loc_154 : location_info := LocationInfo file_0 57 2 57 9.
  Definition loc_155 : location_info := LocationInfo file_0 57 2 57 9.
  Definition loc_156 : location_info := LocationInfo file_0 57 10 57 31.
  Definition loc_157 : location_info := LocationInfo file_0 57 11 57 31.
  Definition loc_158 : location_info := LocationInfo file_0 57 11 57 26.
  Definition loc_159 : location_info := LocationInfo file_0 55 2 55 13.
  Definition loc_160 : location_info := LocationInfo file_0 55 2 55 7.
  Definition loc_161 : location_info := LocationInfo file_0 55 2 55 7.
  Definition loc_162 : location_info := LocationInfo file_0 55 16 55 20.
  Definition loc_163 : location_info := LocationInfo file_0 55 16 55 20.
  Definition loc_164 : location_info := LocationInfo file_0 54 30 54 33.
  Definition loc_165 : location_info := LocationInfo file_0 54 30 54 33.
  Definition loc_168 : location_info := LocationInfo file_0 49 41 52 3.
  Definition loc_169 : location_info := LocationInfo file_0 51 4 51 11.
  Definition loc_172 : location_info := LocationInfo file_0 49 6 49 39.
  Definition loc_173 : location_info := LocationInfo file_0 49 6 49 10.
  Definition loc_174 : location_info := LocationInfo file_0 49 6 49 10.
  Definition loc_175 : location_info := LocationInfo file_0 49 13 49 39.
  Definition loc_178 : location_info := LocationInfo file_0 79 2 79 25.
  Definition loc_179 : location_info := LocationInfo file_0 79 9 79 24.
  Definition loc_180 : location_info := LocationInfo file_0 79 9 79 14.
  Definition loc_181 : location_info := LocationInfo file_0 79 9 79 14.
  Definition loc_182 : location_info := LocationInfo file_0 79 15 79 23.
  Definition loc_183 : location_info := LocationInfo file_0 79 15 79 16.
  Definition loc_184 : location_info := LocationInfo file_0 79 15 79 16.
  Definition loc_185 : location_info := LocationInfo file_0 79 19 79 23.
  Definition loc_186 : location_info := LocationInfo file_0 79 19 79 23.
  Definition loc_189 : location_info := LocationInfo file_0 84 2 84 22.
  Definition loc_190 : location_info := LocationInfo file_0 84 2 84 6.
  Definition loc_191 : location_info := LocationInfo file_0 84 2 84 6.
  Definition loc_192 : location_info := LocationInfo file_0 84 7 84 15.
  Definition loc_193 : location_info := LocationInfo file_0 84 7 84 8.
  Definition loc_194 : location_info := LocationInfo file_0 84 7 84 8.
  Definition loc_195 : location_info := LocationInfo file_0 84 11 84 15.
  Definition loc_196 : location_info := LocationInfo file_0 84 11 84 15.
  Definition loc_197 : location_info := LocationInfo file_0 84 17 84 20.
  Definition loc_198 : location_info := LocationInfo file_0 84 17 84 20.
  Definition loc_201 : location_info := LocationInfo file_0 67 2 67 33.
  Definition loc_202 : location_info := LocationInfo file_0 68 2 68 40.
  Definition loc_203 : location_info := LocationInfo file_0 72 2 72 12.
  Definition loc_204 : location_info := LocationInfo file_0 72 12 72 13.
  Definition loc_205 : location_info := LocationInfo file_0 74 2 74 49.
  Definition loc_206 : location_info := LocationInfo file_0 74 49 74 3.
  Definition loc_207 : location_info := LocationInfo file_0 74 30 74 48.
  Definition loc_208 : location_info := LocationInfo file_0 74 31 74 48.
  Definition loc_209 : location_info := LocationInfo file_0 72 2 72 12.
  Definition loc_210 : location_info := LocationInfo file_0 72 10 72 12.
  Definition loc_211 : location_info := LocationInfo file_0 72 2 72 12.
  Definition loc_212 : location_info := LocationInfo file_0 72 2 72 12.
  Definition loc_213 : location_info := LocationInfo file_0 72 8 72 9.
  Definition loc_214 : location_info := LocationInfo file_0 68 2 68 22.
  Definition loc_215 : location_info := LocationInfo file_0 68 2 68 17.
  Definition loc_216 : location_info := LocationInfo file_0 68 25 68 39.
  Definition loc_217 : location_info := LocationInfo file_0 67 2 67 9.
  Definition loc_218 : location_info := LocationInfo file_0 67 2 67 9.
  Definition loc_219 : location_info := LocationInfo file_0 67 10 67 31.
  Definition loc_220 : location_info := LocationInfo file_0 67 11 67 31.
  Definition loc_221 : location_info := LocationInfo file_0 67 11 67 26.

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
        locinfo: loc_2 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_124 ;
        if: LocInfoE loc_124 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_124 (i2v 1 i32)))
        then
        locinfo: loc_5 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_23 ;
        Goto "#8"
      ]> $
      <[ "#11" :=
        locinfo: loc_74 ;
        LocInfoE loc_85 (!{void*} (LocInfoE loc_86 ("prev"))) <-{ void* }
          LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ((LocInfoE loc_89 (!{void*} (LocInfoE loc_90 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_75 ;
        expr: (LocInfoE loc_75 (Call (LocInfoE loc_80 (global_sl_unlock)) [@{expr} LocInfoE loc_81 (AnnotExpr 1%nat LockA (LocInfoE loc_81 (&(LocInfoE loc_82 ((LocInfoE loc_83 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_76 ;
        Return (LocInfoE loc_77 (use{void*} (LocInfoE loc_78 ("cur"))))
      ]> $
      <[ "#12" :=
        locinfo: loc_64 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_5 ;
        expr: (LocInfoE loc_5 (Call (LocInfoE loc_120 (global_sl_lock)) [@{expr} LocInfoE loc_121 (&(LocInfoE loc_122 ((LocInfoE loc_123 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_6 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_116 (&(LocInfoE loc_117 ((LocInfoE loc_118 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        "prev" <-{ void* }
          LocInfoE loc_111 (&(LocInfoE loc_112 ((LocInfoE loc_113 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_9 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        Return (VOID)
      ]> $
      <[ "#4" :=
        locinfo: loc_105 ;
        if: LocInfoE loc_105 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_105 ((LocInfoE loc_106 (use{void*} (LocInfoE loc_108 (!{void*} (LocInfoE loc_109 ("prev")))))) !={PtrOp, PtrOp} (LocInfoE loc_110 (NULL)))))
        then
        Goto "#5"
        else
        locinfo: loc_10 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        "cur" <-{ void* }
          LocInfoE loc_99 (use{void*} (LocInfoE loc_101 (!{void*} (LocInfoE loc_102 ("prev"))))) ;
        locinfo: loc_92 ;
        if: LocInfoE loc_92 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_92 ((LocInfoE loc_93 (use{it_layout size_t} (LocInfoE loc_94 ((LocInfoE loc_95 (!{void*} (LocInfoE loc_96 ("cur")))) at{struct_alloc_entry} "size")))) ={IntOp size_t, IntOp size_t} (LocInfoE loc_97 (use{it_layout size_t} (LocInfoE loc_98 ("size")))))))
        then
        locinfo: loc_74 ;
          Goto "#11"
        else
        locinfo: loc_64 ;
          Goto "#12"
      ]> $
      <[ "#6" :=
        locinfo: loc_10 ;
        expr: (LocInfoE loc_10 (Call (LocInfoE loc_14 (global_sl_unlock)) [@{expr} LocInfoE loc_15 (AnnotExpr 1%nat LockA (LocInfoE loc_15 (&(LocInfoE loc_16 ((LocInfoE loc_17 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_11 ;
        Goto "continue2"
      ]> $
      <[ "#7" :=
        locinfo: loc_64 ;
        if: LocInfoE loc_64 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_64 ((LocInfoE loc_65 (use{it_layout size_t} (LocInfoE loc_66 ((LocInfoE loc_67 (!{void*} (LocInfoE loc_68 ("cur")))) at{struct_alloc_entry} "size")))) ≥{IntOp size_t, IntOp size_t} (LocInfoE loc_69 ((LocInfoE loc_70 (use{it_layout size_t} (LocInfoE loc_71 ("size")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_72 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))))
        then
        locinfo: loc_32 ;
          Goto "#9"
        else
        locinfo: loc_23 ;
          Goto "#10"
      ]> $
      <[ "#8" :=
        locinfo: loc_23 ;
        LocInfoE loc_26 ("prev") <-{ void* }
          LocInfoE loc_27 (&(LocInfoE loc_28 ((LocInfoE loc_29 (!{void*} (LocInfoE loc_30 ("cur")))) at{struct_alloc_entry} "next"))) ;
        locinfo: loc_24 ;
        Goto "continue4"
      ]> $
      <[ "#9" :=
        locinfo: loc_32 ;
        LocInfoE loc_53 ((LocInfoE loc_54 (!{void*} (LocInfoE loc_55 ("cur")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_56 ((LocInfoE loc_57 (use{it_layout size_t} (LocInfoE loc_58 ((LocInfoE loc_59 (!{void*} (LocInfoE loc_60 ("cur")))) at{struct_alloc_entry} "size")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_61 (use{it_layout size_t} (LocInfoE loc_62 ("size"))))) ;
        "ret" <-{ void* }
          LocInfoE loc_43 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_43 ((LocInfoE loc_44 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_45 (use{void*} (LocInfoE loc_46 ("cur")))))) at_offset{it_layout u8, PtrOp, IntOp size_t} (LocInfoE loc_47 (use{it_layout size_t} (LocInfoE loc_48 ((LocInfoE loc_49 (!{void*} (LocInfoE loc_50 ("cur")))) at{struct_alloc_entry} "size"))))))) ;
        locinfo: loc_34 ;
        expr: (LocInfoE loc_34 (Call (LocInfoE loc_39 (global_sl_unlock)) [@{expr} LocInfoE loc_40 (AnnotExpr 1%nat LockA (LocInfoE loc_40 (&(LocInfoE loc_41 ((LocInfoE loc_42 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        locinfo: loc_35 ;
        Return (LocInfoE loc_36 (use{void*} (LocInfoE loc_37 ("ret"))))
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
        locinfo: loc_172 ;
        if: LocInfoE loc_172 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_172 ((LocInfoE loc_173 (use{it_layout size_t} (LocInfoE loc_174 ("size")))) <{IntOp size_t, IntOp size_t} (LocInfoE loc_175 (i2v (layout_of struct_alloc_entry).(ly_size) size_t)))))
        then
        locinfo: loc_169 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ void* }
          LocInfoE loc_164 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_164 (use{void*} (LocInfoE loc_165 ("ptr"))))) ;
        locinfo: loc_129 ;
        LocInfoE loc_159 ((LocInfoE loc_160 (!{void*} (LocInfoE loc_161 ("entry")))) at{struct_alloc_entry} "size") <-{ it_layout size_t }
          LocInfoE loc_162 (use{it_layout size_t} (LocInfoE loc_163 ("size"))) ;
        locinfo: loc_130 ;
        expr: (LocInfoE loc_130 (Call (LocInfoE loc_155 (global_sl_lock)) [@{expr} LocInfoE loc_156 (&(LocInfoE loc_157 ((LocInfoE loc_158 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_131 ;
        annot: (UnlockA) ;
        expr: (LocInfoE loc_151 (&(LocInfoE loc_152 ((LocInfoE loc_153 (global_allocator_state)) at{struct_alloc_state} "data")))) ;
        locinfo: loc_133 ;
        LocInfoE loc_145 ((LocInfoE loc_146 (!{void*} (LocInfoE loc_147 ("entry")))) at{struct_alloc_entry} "next") <-{ void* }
          LocInfoE loc_148 (use{void*} (LocInfoE loc_149 ((LocInfoE loc_150 (global_allocator_state)) at{struct_alloc_state} "data"))) ;
        locinfo: loc_134 ;
        LocInfoE loc_141 ((LocInfoE loc_142 (global_allocator_state)) at{struct_alloc_state} "data") <-{ void* }
          LocInfoE loc_143 (use{void*} (LocInfoE loc_144 ("entry"))) ;
        locinfo: loc_135 ;
        expr: (LocInfoE loc_135 (Call (LocInfoE loc_137 (global_sl_unlock)) [@{expr} LocInfoE loc_138 (AnnotExpr 1%nat LockA (LocInfoE loc_138 (&(LocInfoE loc_139 ((LocInfoE loc_140 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_169 ;
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
        locinfo: loc_178 ;
        Return (LocInfoE loc_179 (Call (LocInfoE loc_181 (global_alloc)) [@{expr} LocInfoE loc_182 ((LocInfoE loc_183 (use{it_layout size_t} (LocInfoE loc_184 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_185 (use{it_layout size_t} (LocInfoE loc_186 ("size"))))) ]))
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
        locinfo: loc_189 ;
        expr: (LocInfoE loc_189 (Call (LocInfoE loc_191 (global_free)) [@{expr} LocInfoE loc_192 ((LocInfoE loc_193 (use{it_layout size_t} (LocInfoE loc_194 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_195 (use{it_layout size_t} (LocInfoE loc_196 ("size"))))) ;
        LocInfoE loc_197 (use{void*} (LocInfoE loc_198 ("ptr"))) ])) ;
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
        locinfo: loc_201 ;
        expr: (LocInfoE loc_201 (Call (LocInfoE loc_218 (global_sl_init)) [@{expr} LocInfoE loc_219 (&(LocInfoE loc_220 ((LocInfoE loc_221 (global_allocator_state)) at{struct_alloc_state} "lock"))) ])) ;
        locinfo: loc_202 ;
        LocInfoE loc_214 ((LocInfoE loc_215 (global_allocator_state)) at{struct_alloc_state} "data") <-{ void* }
          LocInfoE loc_216 (NULL) ;
        locinfo: loc_203 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_213 ;
        if: LocInfoE loc_213 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_213 (i2v 0 i32)))
        then
        locinfo: loc_211 ;
          Goto "#2"
        else
        locinfo: loc_205 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_211 ;
        Goto "continue13"
      ]> $
      <[ "#3" :=
        locinfo: loc_205 ;
        annot: (ShareAnnot) ;
        expr: (LocInfoE loc_207 (&(LocInfoE loc_208 (global_allocator_state)))) ;
        Return (VOID)
      ]> $
      <[ "continue13" :=
        locinfo: loc_203 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
