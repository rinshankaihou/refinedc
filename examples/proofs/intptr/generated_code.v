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
  Definition loc_130 : location_info := LocationInfo file_0 100 2 100 22.
  Definition loc_131 : location_info := LocationInfo file_0 101 2 101 92.
  Definition loc_132 : location_info := LocationInfo file_0 101 9 101 91.
  Definition loc_133 : location_info := LocationInfo file_0 101 35 101 38.
  Definition loc_134 : location_info := LocationInfo file_0 101 35 101 38.
  Definition loc_135 : location_info := LocationInfo file_0 101 40 101 43.
  Definition loc_136 : location_info := LocationInfo file_0 101 40 101 43.
  Definition loc_137 : location_info := LocationInfo file_0 100 16 100 21.
  Definition loc_138 : location_info := LocationInfo file_0 100 16 100 17.
  Definition loc_139 : location_info := LocationInfo file_0 100 16 100 17.
  Definition loc_140 : location_info := LocationInfo file_0 100 20 100 21.
  Definition loc_143 : location_info := LocationInfo file_0 99 16 99 29.
  Definition loc_144 : location_info := LocationInfo file_0 99 28 99 29.
  Definition loc_145 : location_info := LocationInfo file_0 99 28 99 29.
  Definition loc_150 : location_info := LocationInfo file_0 110 2 110 30.
  Definition loc_151 : location_info := LocationInfo file_0 111 2 111 20.
  Definition loc_152 : location_info := LocationInfo file_0 112 2 112 13.
  Definition loc_153 : location_info := LocationInfo file_0 113 2 113 11.
  Definition loc_154 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_155 : location_info := LocationInfo file_0 113 9 113 10.
  Definition loc_156 : location_info := LocationInfo file_0 112 10 112 12.
  Definition loc_157 : location_info := LocationInfo file_0 112 10 112 12.
  Definition loc_158 : location_info := LocationInfo file_0 112 11 112 12.
  Definition loc_159 : location_info := LocationInfo file_0 112 11 112 12.
  Definition loc_162 : location_info := LocationInfo file_0 111 11 111 19.
  Definition loc_163 : location_info := LocationInfo file_0 111 18 111 19.
  Definition loc_164 : location_info := LocationInfo file_0 111 18 111 19.
  Definition loc_167 : location_info := LocationInfo file_0 110 16 110 29.
  Definition loc_168 : location_info := LocationInfo file_0 110 28 110 29.
  Definition loc_169 : location_info := LocationInfo file_0 110 28 110 29.
  Definition loc_174 : location_info := LocationInfo file_0 122 2 122 30.
  Definition loc_175 : location_info := LocationInfo file_0 123 2 123 22.
  Definition loc_176 : location_info := LocationInfo file_0 124 2 124 101.
  Definition loc_177 : location_info := LocationInfo file_0 125 2 125 13.
  Definition loc_178 : location_info := LocationInfo file_0 126 2 126 11.
  Definition loc_179 : location_info := LocationInfo file_0 126 9 126 10.
  Definition loc_180 : location_info := LocationInfo file_0 126 9 126 10.
  Definition loc_181 : location_info := LocationInfo file_0 125 10 125 12.
  Definition loc_182 : location_info := LocationInfo file_0 125 10 125 12.
  Definition loc_183 : location_info := LocationInfo file_0 125 11 125 12.
  Definition loc_184 : location_info := LocationInfo file_0 125 11 125 12.
  Definition loc_187 : location_info := LocationInfo file_0 124 11 124 100.
  Definition loc_188 : location_info := LocationInfo file_0 124 18 124 100.
  Definition loc_189 : location_info := LocationInfo file_0 124 44 124 47.
  Definition loc_190 : location_info := LocationInfo file_0 124 44 124 47.
  Definition loc_191 : location_info := LocationInfo file_0 124 49 124 52.
  Definition loc_192 : location_info := LocationInfo file_0 124 49 124 52.
  Definition loc_195 : location_info := LocationInfo file_0 123 16 123 21.
  Definition loc_196 : location_info := LocationInfo file_0 123 16 123 17.
  Definition loc_197 : location_info := LocationInfo file_0 123 16 123 17.
  Definition loc_198 : location_info := LocationInfo file_0 123 20 123 21.
  Definition loc_201 : location_info := LocationInfo file_0 122 16 122 29.
  Definition loc_202 : location_info := LocationInfo file_0 122 28 122 29.
  Definition loc_203 : location_info := LocationInfo file_0 122 28 122 29.
  Definition loc_208 : location_info := LocationInfo file_0 135 2 135 30.
  Definition loc_209 : location_info := LocationInfo file_0 136 2 136 113.
  Definition loc_210 : location_info := LocationInfo file_0 137 2 137 12.
  Definition loc_211 : location_info := LocationInfo file_0 137 9 137 11.
  Definition loc_212 : location_info := LocationInfo file_0 137 9 137 11.
  Definition loc_213 : location_info := LocationInfo file_0 137 10 137 11.
  Definition loc_214 : location_info := LocationInfo file_0 137 10 137 11.
  Definition loc_215 : location_info := LocationInfo file_0 136 11 136 112.
  Definition loc_216 : location_info := LocationInfo file_0 136 18 136 112.
  Definition loc_217 : location_info := LocationInfo file_0 136 44 136 47.
  Definition loc_218 : location_info := LocationInfo file_0 136 44 136 47.
  Definition loc_219 : location_info := LocationInfo file_0 136 49 136 56.
  Definition loc_220 : location_info := LocationInfo file_0 136 50 136 51.
  Definition loc_221 : location_info := LocationInfo file_0 136 50 136 51.
  Definition loc_222 : location_info := LocationInfo file_0 136 54 136 55.
  Definition loc_225 : location_info := LocationInfo file_0 135 16 135 29.
  Definition loc_226 : location_info := LocationInfo file_0 135 28 135 29.
  Definition loc_227 : location_info := LocationInfo file_0 135 28 135 29.
  Definition loc_232 : location_info := LocationInfo file_0 146 2 146 30.
  Definition loc_233 : location_info := LocationInfo file_0 147 2 147 22.
  Definition loc_234 : location_info := LocationInfo file_0 148 2 148 101.
  Definition loc_235 : location_info := LocationInfo file_0 149 2 149 12.
  Definition loc_236 : location_info := LocationInfo file_0 149 9 149 11.
  Definition loc_237 : location_info := LocationInfo file_0 149 9 149 11.
  Definition loc_238 : location_info := LocationInfo file_0 149 10 149 11.
  Definition loc_239 : location_info := LocationInfo file_0 149 10 149 11.
  Definition loc_240 : location_info := LocationInfo file_0 148 11 148 100.
  Definition loc_241 : location_info := LocationInfo file_0 148 18 148 100.
  Definition loc_242 : location_info := LocationInfo file_0 148 44 148 47.
  Definition loc_243 : location_info := LocationInfo file_0 148 44 148 47.
  Definition loc_244 : location_info := LocationInfo file_0 148 49 148 52.
  Definition loc_245 : location_info := LocationInfo file_0 148 49 148 52.
  Definition loc_248 : location_info := LocationInfo file_0 147 16 147 21.
  Definition loc_249 : location_info := LocationInfo file_0 147 16 147 17.
  Definition loc_250 : location_info := LocationInfo file_0 147 16 147 17.
  Definition loc_251 : location_info := LocationInfo file_0 147 20 147 21.
  Definition loc_254 : location_info := LocationInfo file_0 146 16 146 29.
  Definition loc_255 : location_info := LocationInfo file_0 146 28 146 29.
  Definition loc_256 : location_info := LocationInfo file_0 146 28 146 29.
  Definition loc_261 : location_info := LocationInfo file_0 156 2 156 30.
  Definition loc_262 : location_info := LocationInfo file_0 156 9 156 29.
  Definition loc_263 : location_info := LocationInfo file_0 156 15 156 29.

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
      ("k", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_143 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_144 (use{void*} (LocInfoE loc_145 ("p"))))) ;
        "k" <-{ it_layout uintptr_t }
          LocInfoE loc_137 ((LocInfoE loc_138 (use{it_layout uintptr_t} (LocInfoE loc_139 ("i")))) +{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_140 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_140 (i2v 0 i32))))) ;
        locinfo: loc_131 ;
        Return (LocInfoE loc_132 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_135 (use{it_layout uintptr_t} (LocInfoE loc_136 ("k")))) (LocInfoE loc_133 (use{void*} (LocInfoE loc_134 ("p"))))))
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
          LocInfoE loc_167 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_168 (use{void*} (LocInfoE loc_169 ("p"))))) ;
        "q" <-{ void* }
          LocInfoE loc_162 (UnOp (CastOp $ PtrOp) (IntOp uintptr_t) (LocInfoE loc_163 (use{it_layout uintptr_t} (LocInfoE loc_164 ("i"))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_156 (use{it_layout i32} (LocInfoE loc_158 (!{void*} (LocInfoE loc_159 ("q"))))) ;
        locinfo: loc_153 ;
        Return (LocInfoE loc_154 (use{it_layout i32} (LocInfoE loc_155 ("r"))))
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
      ("q", void*);
      ("j", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_201 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_202 (use{void*} (LocInfoE loc_203 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_195 ((LocInfoE loc_196 (use{it_layout uintptr_t} (LocInfoE loc_197 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_198 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_198 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_187 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_188 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_191 (use{it_layout uintptr_t} (LocInfoE loc_192 ("j")))) (LocInfoE loc_189 (use{void*} (LocInfoE loc_190 ("p"))))))) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_181 (use{it_layout i32} (LocInfoE loc_183 (!{void*} (LocInfoE loc_184 ("q"))))) ;
        locinfo: loc_178 ;
        Return (LocInfoE loc_179 (use{it_layout i32} (LocInfoE loc_180 ("r"))))
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
          LocInfoE loc_215 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_216 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_219 ((LocInfoE loc_220 (use{it_layout uintptr_t} (LocInfoE loc_221 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_222 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_222 (i2v 1 i32)))))) (LocInfoE loc_217 (use{void*} (LocInfoE loc_218 ("p"))))))) ;
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
      ("q", void*);
      ("j", it_layout uintptr_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout uintptr_t }
          LocInfoE loc_254 (UnOp (CastOp $ IntOp uintptr_t) (PtrOp) (LocInfoE loc_255 (use{void*} (LocInfoE loc_256 ("p"))))) ;
        "j" <-{ it_layout uintptr_t }
          LocInfoE loc_248 ((LocInfoE loc_249 (use{it_layout uintptr_t} (LocInfoE loc_250 ("i")))) ×{IntOp uintptr_t, IntOp uintptr_t} (LocInfoE loc_251 (UnOp (CastOp $ IntOp uintptr_t) (IntOp i32) (LocInfoE loc_251 (i2v 1 i32))))) ;
        "q" <-{ void* }
          LocInfoE loc_240 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_241 (CopyAllocId (IntOp uintptr_t) (LocInfoE loc_244 (use{it_layout uintptr_t} (LocInfoE loc_245 ("j")))) (LocInfoE loc_242 (use{void*} (LocInfoE loc_243 ("p"))))))) ;
        locinfo: loc_235 ;
        Return (LocInfoE loc_236 (use{it_layout i32} (LocInfoE loc_238 (!{void*} (LocInfoE loc_239 ("q"))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [cast_NULL]. *)
  Definition impl_cast_NULL : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_261 ;
        Return (LocInfoE loc_262 (UnOp (CastOp $ IntOp i32) (PtrOp) (LocInfoE loc_263 (NULL))))
      ]> $∅
    )%E
  |}.
End code.
