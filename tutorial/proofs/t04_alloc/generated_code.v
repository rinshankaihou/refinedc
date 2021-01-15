From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
From refinedc.examples.spinlock Require Import spinlock_annot.
Set Default Proof Using "Type".

(* Generated from [tutorial/t04_alloc.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t04_alloc.c".
  Definition loc_2 : location_info := LocationInfo file_0 13 2 42 3.
  Definition loc_3 : location_info := LocationInfo file_0 13 2 42 3.
  Definition loc_4 : location_info := LocationInfo file_0 13 11 42 3.
  Definition loc_5 : location_info := LocationInfo file_0 14 4 14 35.
  Definition loc_6 : location_info := LocationInfo file_0 15 4 15 53.
  Definition loc_7 : location_info := LocationInfo file_0 15 53 15 5.
  Definition loc_8 : location_info := LocationInfo file_0 18 4 18 48.
  Definition loc_9 : location_info := LocationInfo file_0 23 4 39 5.
  Definition loc_10 : location_info := LocationInfo file_0 41 4 41 37.
  Definition loc_11 : location_info := LocationInfo file_0 13 2 42 3.
  Definition loc_12 : location_info := LocationInfo file_0 13 2 42 3.
  Definition loc_13 : location_info := LocationInfo file_0 41 4 41 13.
  Definition loc_14 : location_info := LocationInfo file_0 41 4 41 13.
  Definition loc_15 : location_info := LocationInfo file_0 41 14 41 35.
  Definition loc_16 : location_info := LocationInfo file_0 41 15 41 35.
  Definition loc_17 : location_info := LocationInfo file_0 41 15 41 30.
  Definition loc_18 : location_info := LocationInfo file_0 23 4 39 5.
  Definition loc_19 : location_info := LocationInfo file_0 23 35 39 5.
  Definition loc_20 : location_info := LocationInfo file_0 24 6 24 32.
  Definition loc_21 : location_info := LocationInfo file_0 26 6 30 7.
  Definition loc_22 : location_info := LocationInfo file_0 31 6 36 7.
  Definition loc_23 : location_info := LocationInfo file_0 38 6 38 24.
  Definition loc_24 : location_info := LocationInfo file_0 23 4 39 5.
  Definition loc_25 : location_info := LocationInfo file_0 23 4 39 5.
  Definition loc_26 : location_info := LocationInfo file_0 38 6 38 10.
  Definition loc_27 : location_info := LocationInfo file_0 38 13 38 23.
  Definition loc_28 : location_info := LocationInfo file_0 38 14 38 23.
  Definition loc_29 : location_info := LocationInfo file_0 38 14 38 17.
  Definition loc_30 : location_info := LocationInfo file_0 38 14 38 17.
  Definition loc_31 : location_info := LocationInfo file_0 31 57 36 7.
  Definition loc_32 : location_info := LocationInfo file_0 32 8 32 26.
  Definition loc_33 : location_info := LocationInfo file_0 33 8 33 54.
  Definition loc_34 : location_info := LocationInfo file_0 34 8 34 41.
  Definition loc_35 : location_info := LocationInfo file_0 35 8 35 19.
  Definition loc_36 : location_info := LocationInfo file_0 35 15 35 18.
  Definition loc_37 : location_info := LocationInfo file_0 35 15 35 18.
  Definition loc_38 : location_info := LocationInfo file_0 34 8 34 17.
  Definition loc_39 : location_info := LocationInfo file_0 34 8 34 17.
  Definition loc_40 : location_info := LocationInfo file_0 34 18 34 39.
  Definition loc_41 : location_info := LocationInfo file_0 34 19 34 39.
  Definition loc_42 : location_info := LocationInfo file_0 34 19 34 34.
  Definition loc_43 : location_info := LocationInfo file_0 33 20 33 53.
  Definition loc_44 : location_info := LocationInfo file_0 33 21 33 40.
  Definition loc_45 : location_info := LocationInfo file_0 33 37 33 40.
  Definition loc_46 : location_info := LocationInfo file_0 33 37 33 40.
  Definition loc_47 : location_info := LocationInfo file_0 33 43 33 52.
  Definition loc_48 : location_info := LocationInfo file_0 33 43 33 52.
  Definition loc_49 : location_info := LocationInfo file_0 33 43 33 46.
  Definition loc_50 : location_info := LocationInfo file_0 33 43 33 46.
  Definition loc_53 : location_info := LocationInfo file_0 32 8 32 17.
  Definition loc_54 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_55 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_56 : location_info := LocationInfo file_0 32 8 32 25.
  Definition loc_57 : location_info := LocationInfo file_0 32 8 32 17.
  Definition loc_58 : location_info := LocationInfo file_0 32 8 32 17.
  Definition loc_59 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_60 : location_info := LocationInfo file_0 32 8 32 11.
  Definition loc_61 : location_info := LocationInfo file_0 32 21 32 25.
  Definition loc_62 : location_info := LocationInfo file_0 32 21 32 25.
  Definition loc_64 : location_info := LocationInfo file_0 31 9 31 55.
  Definition loc_65 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_66 : location_info := LocationInfo file_0 31 9 31 18.
  Definition loc_67 : location_info := LocationInfo file_0 31 9 31 12.
  Definition loc_68 : location_info := LocationInfo file_0 31 9 31 12.
  Definition loc_69 : location_info := LocationInfo file_0 31 22 31 55.
  Definition loc_70 : location_info := LocationInfo file_0 31 22 31 26.
  Definition loc_71 : location_info := LocationInfo file_0 31 22 31 26.
  Definition loc_72 : location_info := LocationInfo file_0 31 29 31 55.
  Definition loc_73 : location_info := LocationInfo file_0 26 28 30 7.
  Definition loc_74 : location_info := LocationInfo file_0 27 8 27 26.
  Definition loc_75 : location_info := LocationInfo file_0 28 8 28 41.
  Definition loc_76 : location_info := LocationInfo file_0 29 8 29 19.
  Definition loc_77 : location_info := LocationInfo file_0 29 15 29 18.
  Definition loc_78 : location_info := LocationInfo file_0 29 15 29 18.
  Definition loc_79 : location_info := LocationInfo file_0 28 8 28 17.
  Definition loc_80 : location_info := LocationInfo file_0 28 8 28 17.
  Definition loc_81 : location_info := LocationInfo file_0 28 18 28 39.
  Definition loc_82 : location_info := LocationInfo file_0 28 19 28 39.
  Definition loc_83 : location_info := LocationInfo file_0 28 19 28 34.
  Definition loc_84 : location_info := LocationInfo file_0 27 8 27 13.
  Definition loc_85 : location_info := LocationInfo file_0 27 9 27 13.
  Definition loc_86 : location_info := LocationInfo file_0 27 9 27 13.
  Definition loc_87 : location_info := LocationInfo file_0 27 16 27 25.
  Definition loc_88 : location_info := LocationInfo file_0 27 16 27 25.
  Definition loc_89 : location_info := LocationInfo file_0 27 16 27 19.
  Definition loc_90 : location_info := LocationInfo file_0 27 16 27 19.
  Definition loc_92 : location_info := LocationInfo file_0 26 9 26 26.
  Definition loc_93 : location_info := LocationInfo file_0 26 9 26 18.
  Definition loc_94 : location_info := LocationInfo file_0 26 9 26 18.
  Definition loc_95 : location_info := LocationInfo file_0 26 9 26 12.
  Definition loc_96 : location_info := LocationInfo file_0 26 9 26 12.
  Definition loc_97 : location_info := LocationInfo file_0 26 22 26 26.
  Definition loc_98 : location_info := LocationInfo file_0 26 22 26 26.
  Definition loc_99 : location_info := LocationInfo file_0 24 26 24 31.
  Definition loc_100 : location_info := LocationInfo file_0 24 26 24 31.
  Definition loc_101 : location_info := LocationInfo file_0 24 27 24 31.
  Definition loc_102 : location_info := LocationInfo file_0 24 27 24 31.
  Definition loc_105 : location_info := LocationInfo file_0 23 10 23 33.
  Definition loc_106 : location_info := LocationInfo file_0 23 10 23 15.
  Definition loc_107 : location_info := LocationInfo file_0 23 10 23 15.
  Definition loc_108 : location_info := LocationInfo file_0 23 11 23 15.
  Definition loc_109 : location_info := LocationInfo file_0 23 11 23 15.
  Definition loc_110 : location_info := LocationInfo file_0 23 19 23 33.
  Definition loc_111 : location_info := LocationInfo file_0 18 26 18 47.
  Definition loc_112 : location_info := LocationInfo file_0 18 27 18 47.
  Definition loc_113 : location_info := LocationInfo file_0 18 27 18 42.
  Definition loc_116 : location_info := LocationInfo file_0 15 29 15 52.
  Definition loc_117 : location_info := LocationInfo file_0 15 30 15 52.
  Definition loc_118 : location_info := LocationInfo file_0 15 31 15 46.
  Definition loc_119 : location_info := LocationInfo file_0 14 4 14 11.
  Definition loc_120 : location_info := LocationInfo file_0 14 4 14 11.
  Definition loc_121 : location_info := LocationInfo file_0 14 12 14 33.
  Definition loc_122 : location_info := LocationInfo file_0 14 13 14 33.
  Definition loc_123 : location_info := LocationInfo file_0 14 13 14 28.
  Definition loc_124 : location_info := LocationInfo file_0 13 8 13 9.
  Definition loc_127 : location_info := LocationInfo file_0 48 2 51 3.
  Definition loc_128 : location_info := LocationInfo file_0 53 2 53 34.
  Definition loc_129 : location_info := LocationInfo file_0 54 2 54 21.
  Definition loc_130 : location_info := LocationInfo file_0 56 2 56 33.
  Definition loc_131 : location_info := LocationInfo file_0 57 2 57 51.
  Definition loc_132 : location_info := LocationInfo file_0 57 51 57 3.
  Definition loc_133 : location_info := LocationInfo file_0 59 2 59 37.
  Definition loc_134 : location_info := LocationInfo file_0 60 2 60 31.
  Definition loc_135 : location_info := LocationInfo file_0 62 2 62 35.
  Definition loc_136 : location_info := LocationInfo file_0 62 2 62 11.
  Definition loc_137 : location_info := LocationInfo file_0 62 2 62 11.
  Definition loc_138 : location_info := LocationInfo file_0 62 12 62 33.
  Definition loc_139 : location_info := LocationInfo file_0 62 13 62 33.
  Definition loc_140 : location_info := LocationInfo file_0 62 13 62 28.
  Definition loc_141 : location_info := LocationInfo file_0 60 2 60 22.
  Definition loc_142 : location_info := LocationInfo file_0 60 2 60 17.
  Definition loc_143 : location_info := LocationInfo file_0 60 25 60 30.
  Definition loc_144 : location_info := LocationInfo file_0 60 25 60 30.
  Definition loc_145 : location_info := LocationInfo file_0 59 2 59 13.
  Definition loc_146 : location_info := LocationInfo file_0 59 2 59 7.
  Definition loc_147 : location_info := LocationInfo file_0 59 2 59 7.
  Definition loc_148 : location_info := LocationInfo file_0 59 16 59 36.
  Definition loc_149 : location_info := LocationInfo file_0 59 16 59 36.
  Definition loc_150 : location_info := LocationInfo file_0 59 16 59 31.
  Definition loc_151 : location_info := LocationInfo file_0 57 27 57 50.
  Definition loc_152 : location_info := LocationInfo file_0 57 28 57 50.
  Definition loc_153 : location_info := LocationInfo file_0 57 29 57 44.
  Definition loc_154 : location_info := LocationInfo file_0 56 2 56 9.
  Definition loc_155 : location_info := LocationInfo file_0 56 2 56 9.
  Definition loc_156 : location_info := LocationInfo file_0 56 10 56 31.
  Definition loc_157 : location_info := LocationInfo file_0 56 11 56 31.
  Definition loc_158 : location_info := LocationInfo file_0 56 11 56 26.
  Definition loc_159 : location_info := LocationInfo file_0 54 2 54 13.
  Definition loc_160 : location_info := LocationInfo file_0 54 2 54 7.
  Definition loc_161 : location_info := LocationInfo file_0 54 2 54 7.
  Definition loc_162 : location_info := LocationInfo file_0 54 16 54 20.
  Definition loc_163 : location_info := LocationInfo file_0 54 16 54 20.
  Definition loc_164 : location_info := LocationInfo file_0 53 30 53 33.
  Definition loc_165 : location_info := LocationInfo file_0 53 30 53 33.
  Definition loc_168 : location_info := LocationInfo file_0 48 41 51 3.
  Definition loc_169 : location_info := LocationInfo file_0 50 4 50 11.
  Definition loc_172 : location_info := LocationInfo file_0 48 6 48 39.
  Definition loc_173 : location_info := LocationInfo file_0 48 6 48 10.
  Definition loc_174 : location_info := LocationInfo file_0 48 6 48 10.
  Definition loc_175 : location_info := LocationInfo file_0 48 13 48 39.
  Definition loc_178 : location_info := LocationInfo file_0 78 2 78 25.
  Definition loc_179 : location_info := LocationInfo file_0 78 9 78 24.
  Definition loc_180 : location_info := LocationInfo file_0 78 9 78 14.
  Definition loc_181 : location_info := LocationInfo file_0 78 9 78 14.
  Definition loc_182 : location_info := LocationInfo file_0 78 15 78 23.
  Definition loc_183 : location_info := LocationInfo file_0 78 15 78 16.
  Definition loc_184 : location_info := LocationInfo file_0 78 15 78 16.
  Definition loc_185 : location_info := LocationInfo file_0 78 19 78 23.
  Definition loc_186 : location_info := LocationInfo file_0 78 19 78 23.
  Definition loc_189 : location_info := LocationInfo file_0 83 2 83 22.
  Definition loc_190 : location_info := LocationInfo file_0 83 2 83 6.
  Definition loc_191 : location_info := LocationInfo file_0 83 2 83 6.
  Definition loc_192 : location_info := LocationInfo file_0 83 7 83 15.
  Definition loc_193 : location_info := LocationInfo file_0 83 7 83 8.
  Definition loc_194 : location_info := LocationInfo file_0 83 7 83 8.
  Definition loc_195 : location_info := LocationInfo file_0 83 11 83 15.
  Definition loc_196 : location_info := LocationInfo file_0 83 11 83 15.
  Definition loc_197 : location_info := LocationInfo file_0 83 17 83 20.
  Definition loc_198 : location_info := LocationInfo file_0 83 17 83 20.
  Definition loc_201 : location_info := LocationInfo file_0 66 2 66 33.
  Definition loc_202 : location_info := LocationInfo file_0 67 2 67 40.
  Definition loc_203 : location_info := LocationInfo file_0 71 2 71 12.
  Definition loc_204 : location_info := LocationInfo file_0 71 12 71 13.
  Definition loc_205 : location_info := LocationInfo file_0 73 2 73 49.
  Definition loc_206 : location_info := LocationInfo file_0 73 49 73 3.
  Definition loc_207 : location_info := LocationInfo file_0 73 30 73 48.
  Definition loc_208 : location_info := LocationInfo file_0 73 31 73 48.
  Definition loc_209 : location_info := LocationInfo file_0 71 2 71 12.
  Definition loc_210 : location_info := LocationInfo file_0 71 10 71 12.
  Definition loc_211 : location_info := LocationInfo file_0 71 2 71 12.
  Definition loc_212 : location_info := LocationInfo file_0 71 2 71 12.
  Definition loc_213 : location_info := LocationInfo file_0 71 8 71 9.
  Definition loc_214 : location_info := LocationInfo file_0 67 2 67 22.
  Definition loc_215 : location_info := LocationInfo file_0 67 2 67 17.
  Definition loc_216 : location_info := LocationInfo file_0 67 25 67 39.
  Definition loc_217 : location_info := LocationInfo file_0 66 2 66 9.
  Definition loc_218 : location_info := LocationInfo file_0 66 2 66 9.
  Definition loc_219 : location_info := LocationInfo file_0 66 10 66 31.
  Definition loc_220 : location_info := LocationInfo file_0 66 11 66 31.
  Definition loc_221 : location_info := LocationInfo file_0 66 11 66 26.

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
        "_" <- LocInfoE loc_80 (global_sl_unlock) with
          [ LocInfoE loc_81 (AnnotExpr 1%nat LockA (LocInfoE loc_81 (&(LocInfoE loc_82 ((LocInfoE loc_83 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
        locinfo: loc_76 ;
        Return (LocInfoE loc_77 (use{void*} (LocInfoE loc_78 ("cur"))))
      ]> $
      <[ "#12" :=
        locinfo: loc_64 ;
        Goto "#7"
      ]> $
      <[ "#2" :=
        locinfo: loc_5 ;
        "_" <- LocInfoE loc_120 (global_sl_lock) with
          [ LocInfoE loc_121 (&(LocInfoE loc_122 ((LocInfoE loc_123 (global_allocator_state)) at{struct_alloc_state} "lock"))) ] ;
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
        "_" <- LocInfoE loc_14 (global_sl_unlock) with
          [ LocInfoE loc_15 (AnnotExpr 1%nat LockA (LocInfoE loc_15 (&(LocInfoE loc_16 ((LocInfoE loc_17 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
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
        "_" <- LocInfoE loc_39 (global_sl_unlock) with
          [ LocInfoE loc_40 (AnnotExpr 1%nat LockA (LocInfoE loc_40 (&(LocInfoE loc_41 ((LocInfoE loc_42 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
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
        "_" <- LocInfoE loc_155 (global_sl_lock) with
          [ LocInfoE loc_156 (&(LocInfoE loc_157 ((LocInfoE loc_158 (global_allocator_state)) at{struct_alloc_state} "lock"))) ] ;
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
        "_" <- LocInfoE loc_137 (global_sl_unlock) with
          [ LocInfoE loc_138 (AnnotExpr 1%nat LockA (LocInfoE loc_138 (&(LocInfoE loc_139 ((LocInfoE loc_140 (global_allocator_state)) at{struct_alloc_state} "lock"))))) ] ;
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
        locinfo: loc_179 ;
        "$0" <- LocInfoE loc_181 (global_alloc) with
          [ LocInfoE loc_182 ((LocInfoE loc_183 (use{it_layout size_t} (LocInfoE loc_184 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_185 (use{it_layout size_t} (LocInfoE loc_186 ("size"))))) ] ;
        locinfo: loc_178 ;
        Return (LocInfoE loc_179 ("$0"))
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
        "_" <- LocInfoE loc_191 (global_free) with
          [ LocInfoE loc_192 ((LocInfoE loc_193 (use{it_layout size_t} (LocInfoE loc_194 ("n")))) ×{IntOp size_t, IntOp size_t} (LocInfoE loc_195 (use{it_layout size_t} (LocInfoE loc_196 ("size"))))) ;
          LocInfoE loc_197 (use{void*} (LocInfoE loc_198 ("ptr"))) ] ;
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
        "_" <- LocInfoE loc_218 (global_sl_init) with
          [ LocInfoE loc_219 (&(LocInfoE loc_220 ((LocInfoE loc_221 (global_allocator_state)) at{struct_alloc_state} "lock"))) ] ;
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
