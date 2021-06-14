From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/intptr.c]. *)
Section code.
  Definition file_0 : string := "examples/intptr.c".
  Definition loc_2 : location_info := LocationInfo file_0 18 2 18 30.
  Definition loc_3 : location_info := LocationInfo file_0 20 2 20 11.
  Definition loc_4 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_5 : location_info := LocationInfo file_0 20 9 20 10.
  Definition loc_6 : location_info := LocationInfo file_0 18 16 18 29.
  Definition loc_7 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_8 : location_info := LocationInfo file_0 18 28 18 29.
  Definition loc_13 : location_info := LocationInfo file_0 28 2 28 30.
  Definition loc_14 : location_info := LocationInfo file_0 29 2 29 11.
  Definition loc_15 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_16 : location_info := LocationInfo file_0 29 9 29 10.
  Definition loc_17 : location_info := LocationInfo file_0 28 16 28 29.
  Definition loc_18 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_19 : location_info := LocationInfo file_0 28 28 28 29.
  Definition loc_24 : location_info := LocationInfo file_0 37 2 37 30.
  Definition loc_25 : location_info := LocationInfo file_0 38 2 38 15.
  Definition loc_26 : location_info := LocationInfo file_0 38 9 38 14.
  Definition loc_27 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_28 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_29 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_30 : location_info := LocationInfo file_0 37 16 37 29.
  Definition loc_31 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_32 : location_info := LocationInfo file_0 37 28 37 29.
  Definition loc_37 : location_info := LocationInfo file_0 46 2 46 32.
  Definition loc_38 : location_info := LocationInfo file_0 47 2 47 32.
  Definition loc_39 : location_info := LocationInfo file_0 49 2 51 3.
  Definition loc_40 : location_info := LocationInfo file_0 53 2 53 12.
  Definition loc_41 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_42 : location_info := LocationInfo file_0 53 9 53 11.
  Definition loc_43 : location_info := LocationInfo file_0 49 14 51 3.
  Definition loc_44 : location_info := LocationInfo file_0 50 4 50 14.
  Definition loc_45 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_46 : location_info := LocationInfo file_0 50 11 50 13.
  Definition loc_48 : location_info := LocationInfo file_0 49 5 49 13.
  Definition loc_49 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_50 : location_info := LocationInfo file_0 49 5 49 7.
  Definition loc_51 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_52 : location_info := LocationInfo file_0 49 11 49 13.
  Definition loc_53 : location_info := LocationInfo file_0 47 17 47 31.
  Definition loc_54 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_55 : location_info := LocationInfo file_0 47 29 47 31.
  Definition loc_58 : location_info := LocationInfo file_0 46 17 46 31.
  Definition loc_59 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_60 : location_info := LocationInfo file_0 46 29 46 31.
  Definition loc_65 : location_info := LocationInfo file_0 61 2 61 32.
  Definition loc_66 : location_info := LocationInfo file_0 62 2 62 32.
  Definition loc_67 : location_info := LocationInfo file_0 64 2 66 3.
  Definition loc_68 : location_info := LocationInfo file_0 68 2 68 12.
  Definition loc_69 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_70 : location_info := LocationInfo file_0 68 9 68 11.
  Definition loc_71 : location_info := LocationInfo file_0 64 14 66 3.
  Definition loc_72 : location_info := LocationInfo file_0 65 4 65 14.
  Definition loc_73 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_74 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_76 : location_info := LocationInfo file_0 64 5 64 13.
  Definition loc_77 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_78 : location_info := LocationInfo file_0 64 5 64 7.
  Definition loc_79 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_80 : location_info := LocationInfo file_0 64 11 64 13.
  Definition loc_81 : location_info := LocationInfo file_0 62 17 62 31.
  Definition loc_82 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_83 : location_info := LocationInfo file_0 62 29 62 31.
  Definition loc_86 : location_info := LocationInfo file_0 61 17 61 31.
  Definition loc_87 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_88 : location_info := LocationInfo file_0 61 29 61 31.
  Definition loc_93 : location_info := LocationInfo file_0 78 2 78 30.
  Definition loc_94 : location_info := LocationInfo file_0 79 2 79 22.
  Definition loc_95 : location_info := LocationInfo file_0 80 2 80 11.
  Definition loc_96 : location_info := LocationInfo file_0 80 9 80 10.
  Definition loc_97 : location_info := LocationInfo file_0 80 9 80 10.
  Definition loc_98 : location_info := LocationInfo file_0 79 12 79 21.
  Definition loc_99 : location_info := LocationInfo file_0 79 20 79 21.
  Definition loc_100 : location_info := LocationInfo file_0 79 20 79 21.
  Definition loc_103 : location_info := LocationInfo file_0 78 16 78 29.
  Definition loc_104 : location_info := LocationInfo file_0 78 28 78 29.
  Definition loc_105 : location_info := LocationInfo file_0 78 28 78 29.
  Definition loc_110 : location_info := LocationInfo file_0 89 2 89 30.
  Definition loc_111 : location_info := LocationInfo file_0 90 2 90 28.
  Definition loc_112 : location_info := LocationInfo file_0 91 2 91 11.
  Definition loc_113 : location_info := LocationInfo file_0 91 9 91 10.
  Definition loc_114 : location_info := LocationInfo file_0 91 9 91 10.
  Definition loc_115 : location_info := LocationInfo file_0 90 12 90 27.
  Definition loc_116 : location_info := LocationInfo file_0 90 20 90 27.
  Definition loc_117 : location_info := LocationInfo file_0 90 21 90 22.
  Definition loc_118 : location_info := LocationInfo file_0 90 21 90 22.
  Definition loc_119 : location_info := LocationInfo file_0 90 25 90 26.
  Definition loc_122 : location_info := LocationInfo file_0 89 16 89 29.
  Definition loc_123 : location_info := LocationInfo file_0 89 28 89 29.
  Definition loc_124 : location_info := LocationInfo file_0 89 28 89 29.
  Definition loc_129 : location_info := LocationInfo file_0 99 2 99 30.
  Definition loc_130 : location_info := LocationInfo file_0 100 2 100 27.
  Definition loc_131 : location_info := LocationInfo file_0 101 2 101 71.
  Definition loc_132 : location_info := LocationInfo file_0 101 9 101 70.
  Definition loc_133 : location_info := LocationInfo file_0 101 35 101 38.
  Definition loc_134 : location_info := LocationInfo file_0 101 35 101 38.
  Definition loc_135 : location_info := LocationInfo file_0 101 40 101 43.
  Definition loc_136 : location_info := LocationInfo file_0 101 40 101 43.
  Definition loc_137 : location_info := LocationInfo file_0 100 11 100 26.
  Definition loc_138 : location_info := LocationInfo file_0 100 19 100 26.
  Definition loc_139 : location_info := LocationInfo file_0 100 20 100 21.
  Definition loc_140 : location_info := LocationInfo file_0 100 20 100 21.
  Definition loc_141 : location_info := LocationInfo file_0 100 24 100 25.
  Definition loc_144 : location_info := LocationInfo file_0 99 16 99 29.
  Definition loc_145 : location_info := LocationInfo file_0 99 28 99 29.
  Definition loc_146 : location_info := LocationInfo file_0 99 28 99 29.
  Definition loc_151 : location_info := LocationInfo file_0 110 2 110 30.
  Definition loc_152 : location_info := LocationInfo file_0 111 2 111 20.
  Definition loc_153 : location_info := LocationInfo file_0 112 2 112 13.
  Definition loc_154 : location_info := LocationInfo file_0 113 2 113 11.
  Definition loc_155 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_156 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_157 : location_info := LocationInfo file_0 112 10 112 12.
  Definition loc_158 : location_info := LocationInfo file_0 112 10 112 12.
  Definition loc_159 : location_info := LocationInfo file_0 112 11 112 12.
  Definition loc_160 : location_info := LocationInfo file_0 112 11 112 12.
  Definition loc_163 : location_info := LocationInfo file_0 111 11 111 19.
  Definition loc_164 : location_info := LocationInfo file_0 111 18 111 19.
  Definition loc_165 : location_info := LocationInfo file_0 111 18 111 19.
  Definition loc_168 : location_info := LocationInfo file_0 110 16 110 29.
  Definition loc_169 : location_info := LocationInfo file_0 110 28 110 29.
  Definition loc_170 : location_info := LocationInfo file_0 110 28 110 29.
  Definition loc_175 : location_info := LocationInfo file_0 122 2 122 30.
  Definition loc_176 : location_info := LocationInfo file_0 123 2 123 26.
  Definition loc_177 : location_info := LocationInfo file_0 124 2 124 68.
  Definition loc_178 : location_info := LocationInfo file_0 125 2 125 13.
  Definition loc_179 : location_info := LocationInfo file_0 126 2 126 11.
  Definition loc_180 : location_info := LocationInfo file_0 126 9 126 10.
  Definition loc_181 : location_info := LocationInfo file_0 126 9 126 10.
  Definition loc_182 : location_info := LocationInfo file_0 125 10 125 12.
  Definition loc_183 : location_info := LocationInfo file_0 125 10 125 12.
  Definition loc_184 : location_info := LocationInfo file_0 125 11 125 12.
  Definition loc_185 : location_info := LocationInfo file_0 125 11 125 12.
  Definition loc_188 : location_info := LocationInfo file_0 124 2 124 3.
  Definition loc_189 : location_info := LocationInfo file_0 124 6 124 67.
  Definition loc_190 : location_info := LocationInfo file_0 124 32 124 35.
  Definition loc_191 : location_info := LocationInfo file_0 124 32 124 35.
  Definition loc_192 : location_info := LocationInfo file_0 124 37 124 40.
  Definition loc_193 : location_info := LocationInfo file_0 124 37 124 40.
  Definition loc_194 : location_info := LocationInfo file_0 123 11 123 25.
  Definition loc_195 : location_info := LocationInfo file_0 123 18 123 25.
  Definition loc_196 : location_info := LocationInfo file_0 123 19 123 20.
  Definition loc_197 : location_info := LocationInfo file_0 123 19 123 20.
  Definition loc_198 : location_info := LocationInfo file_0 123 23 123 24.
  Definition loc_201 : location_info := LocationInfo file_0 122 16 122 29.
  Definition loc_202 : location_info := LocationInfo file_0 122 28 122 29.
  Definition loc_203 : location_info := LocationInfo file_0 122 28 122 29.
  Definition loc_208 : location_info := LocationInfo file_0 135 2 135 30.
  Definition loc_209 : location_info := LocationInfo file_0 136 2 136 99.
  Definition loc_210 : location_info := LocationInfo file_0 137 2 137 12.
  Definition loc_211 : location_info := LocationInfo file_0 137 9 137 11.
  Definition loc_212 : location_info := LocationInfo file_0 137 9 137 11.
  Definition loc_213 : location_info := LocationInfo file_0 137 10 137 11.
  Definition loc_214 : location_info := LocationInfo file_0 137 10 137 11.
  Definition loc_215 : location_info := LocationInfo file_0 136 11 136 98.
  Definition loc_216 : location_info := LocationInfo file_0 136 37 136 40.
  Definition loc_217 : location_info := LocationInfo file_0 136 37 136 40.
  Definition loc_218 : location_info := LocationInfo file_0 136 42 136 58.
  Definition loc_219 : location_info := LocationInfo file_0 136 50 136 57.
  Definition loc_220 : location_info := LocationInfo file_0 136 51 136 52.
  Definition loc_221 : location_info := LocationInfo file_0 136 51 136 52.
  Definition loc_222 : location_info := LocationInfo file_0 136 55 136 56.
  Definition loc_225 : location_info := LocationInfo file_0 135 16 135 29.
  Definition loc_226 : location_info := LocationInfo file_0 135 28 135 29.
  Definition loc_227 : location_info := LocationInfo file_0 135 28 135 29.
  Definition loc_232 : location_info := LocationInfo file_0 146 2 146 30.
  Definition loc_233 : location_info := LocationInfo file_0 147 2 147 26.
  Definition loc_234 : location_info := LocationInfo file_0 148 2 148 74.
  Definition loc_235 : location_info := LocationInfo file_0 148 9 148 73.
  Definition loc_236 : location_info := LocationInfo file_0 148 9 148 73.
  Definition loc_237 : location_info := LocationInfo file_0 148 10 148 73.
  Definition loc_238 : location_info := LocationInfo file_0 148 37 148 40.
  Definition loc_239 : location_info := LocationInfo file_0 148 37 148 40.
  Definition loc_240 : location_info := LocationInfo file_0 148 42 148 45.
  Definition loc_241 : location_info := LocationInfo file_0 148 42 148 45.
  Definition loc_242 : location_info := LocationInfo file_0 147 11 147 25.
  Definition loc_243 : location_info := LocationInfo file_0 147 18 147 25.
  Definition loc_244 : location_info := LocationInfo file_0 147 19 147 20.
  Definition loc_245 : location_info := LocationInfo file_0 147 19 147 20.
  Definition loc_246 : location_info := LocationInfo file_0 147 23 147 24.
  Definition loc_249 : location_info := LocationInfo file_0 146 16 146 29.
  Definition loc_250 : location_info := LocationInfo file_0 146 28 146 29.
  Definition loc_251 : location_info := LocationInfo file_0 146 28 146 29.
  Definition loc_256 : location_info := LocationInfo file_0 158 2 158 28.
  Definition loc_257 : location_info := LocationInfo file_0 159 2 159 73.
  Definition loc_258 : location_info := LocationInfo file_0 159 9 159 72.
  Definition loc_259 : location_info := LocationInfo file_0 159 36 159 39.
  Definition loc_260 : location_info := LocationInfo file_0 159 36 159 39.
  Definition loc_261 : location_info := LocationInfo file_0 159 41 159 44.
  Definition loc_262 : location_info := LocationInfo file_0 159 41 159 44.
  Definition loc_263 : location_info := LocationInfo file_0 158 12 158 27.
  Definition loc_264 : location_info := LocationInfo file_0 158 20 158 27.
  Definition loc_265 : location_info := LocationInfo file_0 158 21 158 22.
  Definition loc_266 : location_info := LocationInfo file_0 158 21 158 22.
  Definition loc_267 : location_info := LocationInfo file_0 158 25 158 26.

  (* Definition of function [int_ptr1]. *)
  Definition impl_int_ptr1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_6 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_7 (use{void*} (LocInfoE loc_8 ("p"))))) ;
        locinfo: loc_3 ;
        Return (LocInfoE loc_4 (use{it_layout uintptr_t} (LocInfoE loc_5 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_ptr2]. *)
  Definition impl_int_ptr2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_17 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_18 (use{void*} (LocInfoE loc_19 ("p"))))) ;
        locinfo: loc_14 ;
        Return (LocInfoE loc_15 (use{it_layout uintptr_t} (LocInfoE loc_16 ("i"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_ptr3]. *)
  Definition impl_int_ptr3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_30 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_31 (use{void*} (LocInfoE loc_32 ("p"))))) ;
        locinfo: loc_25 ;
        Return (LocInfoE loc_26 ((LocInfoE loc_27 (use{it_layout uintptr_t} (LocInfoE loc_28 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_29 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_29 (i2v 0 i32))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val1]. *)
  Definition impl_min_ptr_val1 : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
      ("i2", it_layout uintptr_t);
      ("i1", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout uintptr_t }
          LocInfoE loc_58 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_59 (use{void*} (LocInfoE loc_60 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_53 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_54 (use{void*} (LocInfoE loc_55 ("p2"))))) ;
        locinfo: loc_48 ;
        if: LocInfoE loc_48 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_48 ((LocInfoE loc_49 (use{it_layout uintptr_t} (LocInfoE loc_50 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_51 (use{it_layout uintptr_t} (LocInfoE loc_52 ("i2")))))))
        then
        locinfo: loc_44 ;
          Goto "#2"
        else
        locinfo: loc_40 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_40 ;
        Return (LocInfoE loc_41 (use{it_layout uintptr_t} (LocInfoE loc_42 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_44 ;
        Return (LocInfoE loc_45 (use{it_layout uintptr_t} (LocInfoE loc_46 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_40 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [min_ptr_val2]. *)
  Definition impl_min_ptr_val2 : function := {|
    f_args := [
      ("p1", void*);
      ("p2", void*)
    ];
    f_local_vars := [
      ("i2", it_layout uintptr_t);
      ("i1", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i1" <-{ it_layout uintptr_t }
          LocInfoE loc_86 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_87 (use{void*} (LocInfoE loc_88 ("p1"))))) ;
        "i2" <-{ it_layout uintptr_t }
          LocInfoE loc_81 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_82 (use{void*} (LocInfoE loc_83 ("p2"))))) ;
        locinfo: loc_76 ;
        if: LocInfoE loc_76 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_76 ((LocInfoE loc_77 (use{it_layout uintptr_t} (LocInfoE loc_78 ("i1")))) ≤{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_79 (use{it_layout uintptr_t} (LocInfoE loc_80 ("i2")))))))
        then
        locinfo: loc_72 ;
          Goto "#2"
        else
        locinfo: loc_68 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (use{it_layout uintptr_t} (LocInfoE loc_70 ("i2"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_72 ;
        Return (LocInfoE loc_73 (use{it_layout uintptr_t} (LocInfoE loc_74 ("i1"))))
      ]> $
      <[ "#3" :=
        locinfo: loc_68 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip1]. *)
  Definition impl_roundtrip1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_103 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_104 (use{void*} (LocInfoE loc_105 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_98 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_99 (use{it_layout uintptr_t} (LocInfoE loc_100 ("i"))))) ;
        locinfo: loc_95 ;
        Return (LocInfoE loc_96 (use{void*} (LocInfoE loc_97 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip2]. *)
  Definition impl_roundtrip2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_122 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_123 (use{void*} (LocInfoE loc_124 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_115 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_116 ((LocInfoE loc_117 (use{it_layout uintptr_t} (LocInfoE loc_118 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_119 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_119 (i2v 0 i32))))))) ;
        locinfo: loc_112 ;
        Return (LocInfoE loc_113 (use{void*} (LocInfoE loc_114 ("q"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip3]. *)
  Definition impl_roundtrip3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_144 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_145 (use{void*} (LocInfoE loc_146 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_137 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_137 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_138 ((LocInfoE loc_139 (use{it_layout uintptr_t} (LocInfoE loc_140 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_141 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_141 (i2v 0 i32))))))))) ;
        locinfo: loc_131 ;
        Return (LocInfoE loc_132 (CopyAllocId (PtrOp) (LocInfoE loc_135 (use{void*} (LocInfoE loc_136 ("q")))) (LocInfoE loc_133 (use{void*} (LocInfoE loc_134 ("p"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read1]. *)
  Definition impl_roundtrip_and_read1 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("r", it_layout i32);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_168 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_169 (use{void*} (LocInfoE loc_170 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_163 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_164 (use{it_layout uintptr_t} (LocInfoE loc_165 ("i"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_157 (use{it_layout i32} (LocInfoE loc_159 (!{void*} (LocInfoE loc_160 ("q"))))) ;
        locinfo: loc_154 ;
        Return (LocInfoE loc_155 (use{it_layout i32} (LocInfoE loc_156 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read2]. *)
  Definition impl_roundtrip_and_read2 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("r", it_layout i32);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_201 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_202 (use{void*} (LocInfoE loc_203 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_194 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_195 ((LocInfoE loc_196 (use{it_layout uintptr_t} (LocInfoE loc_197 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_198 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_198 (i2v 1 i32))))))) ;
        locinfo: loc_177 ;
        LocInfoE loc_188 ("q") <-{ void* }
          LocInfoE loc_189 (CopyAllocId (PtrOp) (LocInfoE loc_192 (use{void*} (LocInfoE loc_193 ("q")))) (LocInfoE loc_190 (use{void*} (LocInfoE loc_191 ("p"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_182 (use{it_layout i32} (LocInfoE loc_184 (!{void*} (LocInfoE loc_185 ("q"))))) ;
        locinfo: loc_179 ;
        Return (LocInfoE loc_180 (use{it_layout i32} (LocInfoE loc_181 ("r"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read3]. *)
  Definition impl_roundtrip_and_read3 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_225 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_226 (use{void*} (LocInfoE loc_227 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_215 (CopyAllocId (PtrOp) (LocInfoE loc_218 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_219 ((LocInfoE loc_220 (use{it_layout uintptr_t} (LocInfoE loc_221 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_222 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_222 (i2v 1 i32)))))))) (LocInfoE loc_216 (use{void*} (LocInfoE loc_217 ("p"))))) ;
        locinfo: loc_210 ;
        Return (LocInfoE loc_211 (use{it_layout i32} (LocInfoE loc_213 (!{void*} (LocInfoE loc_214 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [roundtrip_and_read4]. *)
  Definition impl_roundtrip_and_read4 : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("i", it_layout uintptr_t);
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_249 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_250 (use{void*} (LocInfoE loc_251 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_242 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_243 ((LocInfoE loc_244 (use{it_layout uintptr_t} (LocInfoE loc_245 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_246 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_246 (i2v 1 i32))))))) ;
        locinfo: loc_234 ;
        Return (LocInfoE loc_235 (use{it_layout i32} (LocInfoE loc_237 (LValue (LocInfoE loc_237 (CopyAllocId (PtrOp) (LocInfoE loc_240 (use{void*} (LocInfoE loc_241 ("q")))) (LocInfoE loc_238 (use{void*} (LocInfoE loc_239 ("p"))))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [int_to_ptr]. *)
  Definition impl_int_to_ptr : function := {|
    f_args := [
      ("p", it_layout uintptr_t)
    ];
    f_local_vars := [
      ("q", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "q" <-{ void* }
          LocInfoE loc_263 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_264 ((LocInfoE loc_265 (use{it_layout uintptr_t} (LocInfoE loc_266 ("p")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_267 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_267 (i2v 1 i32))))))) ;
        locinfo: loc_257 ;
        Return (LocInfoE loc_258 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_261 (use{void*} (LocInfoE loc_262 ("q")))) (LocInfoE loc_259 (use{it_layout uintptr_t} (LocInfoE loc_260 ("p"))))))
      ]> $∅
    )%E
  |}.
End code.
