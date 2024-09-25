From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge1.c]. *)
Section code.
  Definition file_0 : string := "examples/VerifyThis2021/challenge1.c".
  Definition loc_2 : location_info := LocationInfo file_0 33 2 33 19.
  Definition loc_3 : location_info := LocationInfo file_0 45 2 47 3.
  Definition loc_4 : location_info := LocationInfo file_0 49 2 51 3.
  Definition loc_5 : location_info := LocationInfo file_0 53 2 53 19.
  Definition loc_6 : location_info := LocationInfo file_0 62 2 64 3.
  Definition loc_7 : location_info := LocationInfo file_0 66 2 66 22.
  Definition loc_8 : location_info := LocationInfo file_0 67 2 67 18.
  Definition loc_9 : location_info := LocationInfo file_0 68 2 68 14.
  Definition loc_10 : location_info := LocationInfo file_0 71 2 71 15.
  Definition loc_11 : location_info := LocationInfo file_0 80 2 86 3.
  Definition loc_12 : location_info := LocationInfo file_0 88 2 88 11.
  Definition loc_13 : location_info := LocationInfo file_0 88 9 88 10.
  Definition loc_14 : location_info := LocationInfo file_0 80 15 86 3.
  Definition loc_15 : location_info := LocationInfo file_0 81 4 81 16.
  Definition loc_16 : location_info := LocationInfo file_0 82 4 82 16.
  Definition loc_17 : location_info := LocationInfo file_0 83 4 83 16.
  Definition loc_18 : location_info := LocationInfo file_0 84 4 84 14.
  Definition loc_19 : location_info := LocationInfo file_0 85 4 85 14.
  Definition loc_20 : location_info := LocationInfo file_0 85 4 85 5.
  Definition loc_21 : location_info := LocationInfo file_0 85 8 85 13.
  Definition loc_22 : location_info := LocationInfo file_0 85 8 85 9.
  Definition loc_23 : location_info := LocationInfo file_0 85 8 85 9.
  Definition loc_24 : location_info := LocationInfo file_0 85 12 85 13.
  Definition loc_25 : location_info := LocationInfo file_0 84 4 84 5.
  Definition loc_26 : location_info := LocationInfo file_0 84 8 84 13.
  Definition loc_27 : location_info := LocationInfo file_0 84 8 84 9.
  Definition loc_28 : location_info := LocationInfo file_0 84 8 84 9.
  Definition loc_29 : location_info := LocationInfo file_0 84 12 84 13.
  Definition loc_30 : location_info := LocationInfo file_0 83 4 83 8.
  Definition loc_31 : location_info := LocationInfo file_0 83 4 83 8.
  Definition loc_32 : location_info := LocationInfo file_0 83 4 83 5.
  Definition loc_33 : location_info := LocationInfo file_0 83 4 83 5.
  Definition loc_34 : location_info := LocationInfo file_0 83 6 83 7.
  Definition loc_35 : location_info := LocationInfo file_0 83 6 83 7.
  Definition loc_36 : location_info := LocationInfo file_0 83 11 83 15.
  Definition loc_37 : location_info := LocationInfo file_0 83 11 83 15.
  Definition loc_38 : location_info := LocationInfo file_0 82 4 82 8.
  Definition loc_39 : location_info := LocationInfo file_0 82 4 82 8.
  Definition loc_40 : location_info := LocationInfo file_0 82 4 82 5.
  Definition loc_41 : location_info := LocationInfo file_0 82 4 82 5.
  Definition loc_42 : location_info := LocationInfo file_0 82 6 82 7.
  Definition loc_43 : location_info := LocationInfo file_0 82 6 82 7.
  Definition loc_44 : location_info := LocationInfo file_0 82 11 82 15.
  Definition loc_45 : location_info := LocationInfo file_0 82 11 82 15.
  Definition loc_46 : location_info := LocationInfo file_0 82 11 82 15.
  Definition loc_47 : location_info := LocationInfo file_0 82 11 82 12.
  Definition loc_48 : location_info := LocationInfo file_0 82 11 82 12.
  Definition loc_49 : location_info := LocationInfo file_0 82 13 82 14.
  Definition loc_50 : location_info := LocationInfo file_0 82 13 82 14.
  Definition loc_51 : location_info := LocationInfo file_0 81 4 81 8.
  Definition loc_52 : location_info := LocationInfo file_0 81 11 81 15.
  Definition loc_53 : location_info := LocationInfo file_0 81 11 81 15.
  Definition loc_54 : location_info := LocationInfo file_0 81 11 81 15.
  Definition loc_55 : location_info := LocationInfo file_0 81 11 81 12.
  Definition loc_56 : location_info := LocationInfo file_0 81 11 81 12.
  Definition loc_57 : location_info := LocationInfo file_0 81 13 81 14.
  Definition loc_58 : location_info := LocationInfo file_0 81 13 81 14.
  Definition loc_59 : location_info := LocationInfo file_0 80 8 80 13.
  Definition loc_60 : location_info := LocationInfo file_0 80 8 80 9.
  Definition loc_61 : location_info := LocationInfo file_0 80 8 80 9.
  Definition loc_62 : location_info := LocationInfo file_0 80 12 80 13.
  Definition loc_63 : location_info := LocationInfo file_0 80 12 80 13.
  Definition loc_64 : location_info := LocationInfo file_0 71 2 71 3.
  Definition loc_65 : location_info := LocationInfo file_0 71 6 71 14.
  Definition loc_66 : location_info := LocationInfo file_0 71 6 71 10.
  Definition loc_67 : location_info := LocationInfo file_0 71 6 71 10.
  Definition loc_68 : location_info := LocationInfo file_0 71 13 71 14.
  Definition loc_69 : location_info := LocationInfo file_0 68 2 68 6.
  Definition loc_70 : location_info := LocationInfo file_0 68 2 68 6.
  Definition loc_71 : location_info := LocationInfo file_0 68 2 68 3.
  Definition loc_72 : location_info := LocationInfo file_0 68 2 68 3.
  Definition loc_73 : location_info := LocationInfo file_0 68 4 68 5.
  Definition loc_74 : location_info := LocationInfo file_0 68 4 68 5.
  Definition loc_75 : location_info := LocationInfo file_0 68 9 68 13.
  Definition loc_76 : location_info := LocationInfo file_0 68 9 68 13.
  Definition loc_77 : location_info := LocationInfo file_0 67 2 67 10.
  Definition loc_78 : location_info := LocationInfo file_0 67 2 67 10.
  Definition loc_79 : location_info := LocationInfo file_0 67 2 67 3.
  Definition loc_80 : location_info := LocationInfo file_0 67 2 67 3.
  Definition loc_81 : location_info := LocationInfo file_0 67 4 67 9.
  Definition loc_82 : location_info := LocationInfo file_0 67 4 67 5.
  Definition loc_83 : location_info := LocationInfo file_0 67 4 67 5.
  Definition loc_84 : location_info := LocationInfo file_0 67 8 67 9.
  Definition loc_85 : location_info := LocationInfo file_0 67 13 67 17.
  Definition loc_86 : location_info := LocationInfo file_0 67 13 67 17.
  Definition loc_87 : location_info := LocationInfo file_0 67 13 67 17.
  Definition loc_88 : location_info := LocationInfo file_0 67 13 67 14.
  Definition loc_89 : location_info := LocationInfo file_0 67 13 67 14.
  Definition loc_90 : location_info := LocationInfo file_0 67 15 67 16.
  Definition loc_91 : location_info := LocationInfo file_0 67 15 67 16.
  Definition loc_92 : location_info := LocationInfo file_0 66 13 66 21.
  Definition loc_93 : location_info := LocationInfo file_0 66 13 66 21.
  Definition loc_94 : location_info := LocationInfo file_0 66 13 66 21.
  Definition loc_95 : location_info := LocationInfo file_0 66 13 66 14.
  Definition loc_96 : location_info := LocationInfo file_0 66 13 66 14.
  Definition loc_97 : location_info := LocationInfo file_0 66 15 66 20.
  Definition loc_98 : location_info := LocationInfo file_0 66 15 66 16.
  Definition loc_99 : location_info := LocationInfo file_0 66 15 66 16.
  Definition loc_100 : location_info := LocationInfo file_0 66 19 66 20.
  Definition loc_103 : location_info := LocationInfo file_0 62 24 64 3.
  Definition loc_104 : location_info := LocationInfo file_0 63 4 63 14.
  Definition loc_105 : location_info := LocationInfo file_0 63 4 63 5.
  Definition loc_106 : location_info := LocationInfo file_0 63 8 63 13.
  Definition loc_107 : location_info := LocationInfo file_0 63 8 63 9.
  Definition loc_108 : location_info := LocationInfo file_0 63 8 63 9.
  Definition loc_109 : location_info := LocationInfo file_0 63 12 63 13.
  Definition loc_110 : location_info := LocationInfo file_0 62 8 62 22.
  Definition loc_111 : location_info := LocationInfo file_0 62 8 62 12.
  Definition loc_112 : location_info := LocationInfo file_0 62 8 62 12.
  Definition loc_113 : location_info := LocationInfo file_0 62 8 62 12.
  Definition loc_114 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_115 : location_info := LocationInfo file_0 62 8 62 9.
  Definition loc_116 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_117 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_118 : location_info := LocationInfo file_0 62 16 62 22.
  Definition loc_119 : location_info := LocationInfo file_0 62 16 62 22.
  Definition loc_120 : location_info := LocationInfo file_0 62 16 62 22.
  Definition loc_121 : location_info := LocationInfo file_0 62 16 62 17.
  Definition loc_122 : location_info := LocationInfo file_0 62 16 62 17.
  Definition loc_123 : location_info := LocationInfo file_0 62 18 62 21.
  Definition loc_124 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_125 : location_info := LocationInfo file_0 62 18 62 19.
  Definition loc_126 : location_info := LocationInfo file_0 62 20 62 21.
  Definition loc_127 : location_info := LocationInfo file_0 53 10 53 18.
  Definition loc_128 : location_info := LocationInfo file_0 53 10 53 14.
  Definition loc_129 : location_info := LocationInfo file_0 53 10 53 14.
  Definition loc_130 : location_info := LocationInfo file_0 53 17 53 18.
  Definition loc_133 : location_info := LocationInfo file_0 49 14 51 3.
  Definition loc_134 : location_info := LocationInfo file_0 50 4 50 13.
  Definition loc_135 : location_info := LocationInfo file_0 50 11 50 12.
  Definition loc_136 : location_info := LocationInfo file_0 49 2 51 3.
  Definition loc_137 : location_info := LocationInfo file_0 49 6 49 12.
  Definition loc_138 : location_info := LocationInfo file_0 49 6 49 7.
  Definition loc_139 : location_info := LocationInfo file_0 49 6 49 7.
  Definition loc_140 : location_info := LocationInfo file_0 49 11 49 12.
  Definition loc_141 : location_info := LocationInfo file_0 45 35 47 3.
  Definition loc_142 : location_info := LocationInfo file_0 46 4 46 14.
  Definition loc_143 : location_info := LocationInfo file_0 46 4 46 5.
  Definition loc_144 : location_info := LocationInfo file_0 46 8 46 13.
  Definition loc_145 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_146 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_147 : location_info := LocationInfo file_0 46 12 46 13.
  Definition loc_148 : location_info := LocationInfo file_0 45 8 45 33.
  Definition loc_149 : location_info := LocationInfo file_0 45 8 45 13.
  Definition loc_150 : location_info := LocationInfo file_0 45 8 45 9.
  Definition loc_151 : location_info := LocationInfo file_0 45 8 45 9.
  Definition loc_152 : location_info := LocationInfo file_0 45 12 45 13.
  Definition loc_153 : location_info := LocationInfo file_0 45 17 45 33.
  Definition loc_154 : location_info := LocationInfo file_0 45 17 45 25.
  Definition loc_155 : location_info := LocationInfo file_0 45 17 45 25.
  Definition loc_156 : location_info := LocationInfo file_0 45 17 45 25.
  Definition loc_157 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_158 : location_info := LocationInfo file_0 45 17 45 18.
  Definition loc_159 : location_info := LocationInfo file_0 45 19 45 24.
  Definition loc_160 : location_info := LocationInfo file_0 45 19 45 20.
  Definition loc_161 : location_info := LocationInfo file_0 45 19 45 20.
  Definition loc_162 : location_info := LocationInfo file_0 45 23 45 24.
  Definition loc_163 : location_info := LocationInfo file_0 45 29 45 33.
  Definition loc_164 : location_info := LocationInfo file_0 45 29 45 33.
  Definition loc_165 : location_info := LocationInfo file_0 45 29 45 33.
  Definition loc_166 : location_info := LocationInfo file_0 45 29 45 30.
  Definition loc_167 : location_info := LocationInfo file_0 45 29 45 30.
  Definition loc_168 : location_info := LocationInfo file_0 45 31 45 32.
  Definition loc_169 : location_info := LocationInfo file_0 45 31 45 32.
  Definition loc_170 : location_info := LocationInfo file_0 33 10 33 18.
  Definition loc_171 : location_info := LocationInfo file_0 33 10 33 14.
  Definition loc_172 : location_info := LocationInfo file_0 33 10 33 14.
  Definition loc_173 : location_info := LocationInfo file_0 33 17 33 18.
  Definition loc_178 : location_info := LocationInfo file_0 145 2 145 24.
  Definition loc_179 : location_info := LocationInfo file_0 146 2 146 12.
  Definition loc_180 : location_info := LocationInfo file_0 149 2 151 3.
  Definition loc_181 : location_info := LocationInfo file_0 153 2 153 16.
  Definition loc_182 : location_info := LocationInfo file_0 154 2 154 29.
  Definition loc_183 : location_info := LocationInfo file_0 155 2 155 22.
  Definition loc_184 : location_info := LocationInfo file_0 163 2 166 3.
  Definition loc_185 : location_info := LocationInfo file_0 169 2 169 11.
  Definition loc_186 : location_info := LocationInfo file_0 169 9 169 10.
  Definition loc_187 : location_info := LocationInfo file_0 169 9 169 10.
  Definition loc_188 : location_info := LocationInfo file_0 163 23 166 3.
  Definition loc_189 : location_info := LocationInfo file_0 164 4 164 31.
  Definition loc_190 : location_info := LocationInfo file_0 165 4 165 24.
  Definition loc_191 : location_info := LocationInfo file_0 165 4 165 13.
  Definition loc_192 : location_info := LocationInfo file_0 165 4 165 13.
  Definition loc_193 : location_info := LocationInfo file_0 165 14 165 16.
  Definition loc_194 : location_info := LocationInfo file_0 165 15 165 16.
  Definition loc_195 : location_info := LocationInfo file_0 165 18 165 22.
  Definition loc_196 : location_info := LocationInfo file_0 165 18 165 22.
  Definition loc_197 : location_info := LocationInfo file_0 164 4 164 8.
  Definition loc_198 : location_info := LocationInfo file_0 164 11 164 30.
  Definition loc_199 : location_info := LocationInfo file_0 164 11 164 21.
  Definition loc_200 : location_info := LocationInfo file_0 164 11 164 21.
  Definition loc_201 : location_info := LocationInfo file_0 164 22 164 23.
  Definition loc_202 : location_info := LocationInfo file_0 164 22 164 23.
  Definition loc_203 : location_info := LocationInfo file_0 164 25 164 29.
  Definition loc_204 : location_info := LocationInfo file_0 164 25 164 29.
  Definition loc_205 : location_info := LocationInfo file_0 163 8 163 21.
  Definition loc_206 : location_info := LocationInfo file_0 163 8 163 12.
  Definition loc_207 : location_info := LocationInfo file_0 163 8 163 12.
  Definition loc_208 : location_info := LocationInfo file_0 163 13 163 14.
  Definition loc_209 : location_info := LocationInfo file_0 163 13 163 14.
  Definition loc_210 : location_info := LocationInfo file_0 163 16 163 20.
  Definition loc_211 : location_info := LocationInfo file_0 163 16 163 20.
  Definition loc_212 : location_info := LocationInfo file_0 155 2 155 11.
  Definition loc_213 : location_info := LocationInfo file_0 155 2 155 11.
  Definition loc_214 : location_info := LocationInfo file_0 155 12 155 14.
  Definition loc_215 : location_info := LocationInfo file_0 155 13 155 14.
  Definition loc_216 : location_info := LocationInfo file_0 155 16 155 20.
  Definition loc_217 : location_info := LocationInfo file_0 155 16 155 20.
  Definition loc_218 : location_info := LocationInfo file_0 154 2 154 6.
  Definition loc_219 : location_info := LocationInfo file_0 154 9 154 28.
  Definition loc_220 : location_info := LocationInfo file_0 154 9 154 19.
  Definition loc_221 : location_info := LocationInfo file_0 154 9 154 19.
  Definition loc_222 : location_info := LocationInfo file_0 154 20 154 21.
  Definition loc_223 : location_info := LocationInfo file_0 154 20 154 21.
  Definition loc_224 : location_info := LocationInfo file_0 154 23 154 27.
  Definition loc_225 : location_info := LocationInfo file_0 154 23 154 27.
  Definition loc_226 : location_info := LocationInfo file_0 153 2 153 6.
  Definition loc_227 : location_info := LocationInfo file_0 153 2 153 6.
  Definition loc_228 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_229 : location_info := LocationInfo file_0 153 7 153 8.
  Definition loc_230 : location_info := LocationInfo file_0 153 10 153 14.
  Definition loc_231 : location_info := LocationInfo file_0 153 10 153 14.
  Definition loc_232 : location_info := LocationInfo file_0 149 17 151 3.
  Definition loc_233 : location_info := LocationInfo file_0 150 4 150 13.
  Definition loc_234 : location_info := LocationInfo file_0 150 11 150 12.
  Definition loc_235 : location_info := LocationInfo file_0 150 11 150 12.
  Definition loc_236 : location_info := LocationInfo file_0 149 2 151 3.
  Definition loc_237 : location_info := LocationInfo file_0 149 6 149 15.
  Definition loc_238 : location_info := LocationInfo file_0 149 6 149 10.
  Definition loc_239 : location_info := LocationInfo file_0 149 6 149 10.
  Definition loc_240 : location_info := LocationInfo file_0 149 14 149 15.
  Definition loc_241 : location_info := LocationInfo file_0 145 13 145 23.
  Definition loc_242 : location_info := LocationInfo file_0 145 13 145 21.
  Definition loc_243 : location_info := LocationInfo file_0 145 13 145 21.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [list]. *)
  Program Definition struct_list := {|
    sl_members := [
      (Some "head", void*);
      (Some "tail", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [next]. *)
  Definition impl_next : function := {|
    f_args := [
      ("A", void*);
      ("size", it_layout i32)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("temp", it_layout i32);
      ("j", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ IntOp i32 }
          LocInfoE loc_170 ((LocInfoE loc_171 (use{IntOp i32} (LocInfoE loc_172 ("size")))) -{IntOp i32, IntOp i32} (LocInfoE loc_173 (i2v 1 i32))) ;
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_148 ;
        if{IntOp i32, None}: LocInfoE loc_148 ((LocInfoE loc_149 ((LocInfoE loc_150 (use{IntOp i32} (LocInfoE loc_151 ("i")))) >{IntOp i32, IntOp i32, i32} (LocInfoE loc_152 (i2v 0 i32)))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_153 ((LocInfoE loc_154 (use{IntOp i32} (LocInfoE loc_156 ((LocInfoE loc_157 (!{PtrOp} (LocInfoE loc_158 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_159 ((LocInfoE loc_160 (use{IntOp i32} (LocInfoE loc_161 ("i")))) -{IntOp i32, IntOp i32} (LocInfoE loc_162 (i2v 1 i32)))))))) ≥{IntOp i32, IntOp i32, i32} (LocInfoE loc_163 (use{IntOp i32} (LocInfoE loc_165 ((LocInfoE loc_166 (!{PtrOp} (LocInfoE loc_167 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_168 (use{IntOp i32} (LocInfoE loc_169 ("i")))))))))))
        then
        locinfo: loc_142 ;
          Goto "#2"
        else
        locinfo: loc_137 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_13 (i2v 1 i32))))
      ]> $
      <[ "#11" :=
        locinfo: loc_134 ;
        Return (LocInfoE loc_135 (UnOp (CastOp $ BoolOp) (IntOp i32) (LocInfoE loc_135 (i2v 0 i32))))
      ]> $
      <[ "#12" :=
        Goto "#4"
      ]> $
      <[ "#2" :=
        locinfo: loc_142 ;
        LocInfoE loc_143 ("i") <-{ IntOp i32 }
          LocInfoE loc_144 ((LocInfoE loc_145 (use{IntOp i32} (LocInfoE loc_146 ("i")))) -{IntOp i32, IntOp i32} (LocInfoE loc_147 (i2v 1 i32))) ;
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_137 ;
        if{IntOp i32, Some "#4"}: LocInfoE loc_137 ((LocInfoE loc_138 (use{IntOp i32} (LocInfoE loc_139 ("i")))) ≤{IntOp i32, IntOp i32, i32} (LocInfoE loc_140 (i2v 0 i32)))
        then
        locinfo: loc_134 ;
          Goto "#11"
        else
        Goto "#12"
      ]> $
      <[ "#4" :=
        "j" <-{ IntOp i32 }
          LocInfoE loc_127 ((LocInfoE loc_128 (use{IntOp i32} (LocInfoE loc_129 ("size")))) -{IntOp i32, IntOp i32} (LocInfoE loc_130 (i2v 1 i32))) ;
        locinfo: loc_6 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_110 ;
        if{IntOp i32, None}: LocInfoE loc_110 ((LocInfoE loc_111 (use{IntOp i32} (LocInfoE loc_113 ((LocInfoE loc_114 (!{PtrOp} (LocInfoE loc_115 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_116 (use{IntOp i32} (LocInfoE loc_117 ("j")))))))) ≤{IntOp i32, IntOp i32, i32} (LocInfoE loc_118 (use{IntOp i32} (LocInfoE loc_120 ((LocInfoE loc_121 (!{PtrOp} (LocInfoE loc_122 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_123 ((LocInfoE loc_124 (use{IntOp i32} (LocInfoE loc_125 ("i")))) -{IntOp i32, IntOp i32} (LocInfoE loc_126 (i2v 1 i32)))))))))
        then
        locinfo: loc_104 ;
          Goto "#6"
        else
        Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_104 ;
        LocInfoE loc_105 ("j") <-{ IntOp i32 }
          LocInfoE loc_106 ((LocInfoE loc_107 (use{IntOp i32} (LocInfoE loc_108 ("j")))) -{IntOp i32, IntOp i32} (LocInfoE loc_109 (i2v 1 i32))) ;
        locinfo: loc_6 ;
        Goto "#5"
      ]> $
      <[ "#7" :=
        "temp" <-{ IntOp i32 }
          LocInfoE loc_92 (use{IntOp i32} (LocInfoE loc_94 ((LocInfoE loc_95 (!{PtrOp} (LocInfoE loc_96 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_97 ((LocInfoE loc_98 (use{IntOp i32} (LocInfoE loc_99 ("i")))) -{IntOp i32, IntOp i32} (LocInfoE loc_100 (i2v 1 i32))))))) ;
        locinfo: loc_8 ;
        LocInfoE loc_78 ((LocInfoE loc_79 (!{PtrOp} (LocInfoE loc_80 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_81 ((LocInfoE loc_82 (use{IntOp i32} (LocInfoE loc_83 ("i")))) -{IntOp i32, IntOp i32} (LocInfoE loc_84 (i2v 1 i32))))) <-{ IntOp i32 }
          LocInfoE loc_85 (use{IntOp i32} (LocInfoE loc_87 ((LocInfoE loc_88 (!{PtrOp} (LocInfoE loc_89 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_90 (use{IntOp i32} (LocInfoE loc_91 ("j"))))))) ;
        locinfo: loc_9 ;
        LocInfoE loc_70 ((LocInfoE loc_71 (!{PtrOp} (LocInfoE loc_72 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_73 (use{IntOp i32} (LocInfoE loc_74 ("j"))))) <-{ IntOp i32 }
          LocInfoE loc_75 (use{IntOp i32} (LocInfoE loc_76 ("temp"))) ;
        locinfo: loc_10 ;
        LocInfoE loc_64 ("j") <-{ IntOp i32 }
          LocInfoE loc_65 ((LocInfoE loc_66 (use{IntOp i32} (LocInfoE loc_67 ("size")))) -{IntOp i32, IntOp i32} (LocInfoE loc_68 (i2v 1 i32))) ;
        locinfo: loc_11 ;
        Goto "#8"
      ]> $
      <[ "#8" :=
        locinfo: loc_59 ;
        if{IntOp i32, None}: LocInfoE loc_59 ((LocInfoE loc_60 (use{IntOp i32} (LocInfoE loc_61 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_62 (use{IntOp i32} (LocInfoE loc_63 ("j")))))
        then
        locinfo: loc_15 ;
          Goto "#9"
        else
        locinfo: loc_12 ;
          Goto "#10"
      ]> $
      <[ "#9" :=
        locinfo: loc_15 ;
        LocInfoE loc_51 ("temp") <-{ IntOp i32 }
          LocInfoE loc_52 (use{IntOp i32} (LocInfoE loc_54 ((LocInfoE loc_55 (!{PtrOp} (LocInfoE loc_56 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_57 (use{IntOp i32} (LocInfoE loc_58 ("i"))))))) ;
        locinfo: loc_16 ;
        LocInfoE loc_39 ((LocInfoE loc_40 (!{PtrOp} (LocInfoE loc_41 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_42 (use{IntOp i32} (LocInfoE loc_43 ("i"))))) <-{ IntOp i32 }
          LocInfoE loc_44 (use{IntOp i32} (LocInfoE loc_46 ((LocInfoE loc_47 (!{PtrOp} (LocInfoE loc_48 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_49 (use{IntOp i32} (LocInfoE loc_50 ("j"))))))) ;
        locinfo: loc_17 ;
        LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("A")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_34 (use{IntOp i32} (LocInfoE loc_35 ("j"))))) <-{ IntOp i32 }
          LocInfoE loc_36 (use{IntOp i32} (LocInfoE loc_37 ("temp"))) ;
        locinfo: loc_18 ;
        LocInfoE loc_25 ("i") <-{ IntOp i32 }
          LocInfoE loc_26 ((LocInfoE loc_27 (use{IntOp i32} (LocInfoE loc_28 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_29 (i2v 1 i32))) ;
        locinfo: loc_19 ;
        LocInfoE loc_20 ("j") <-{ IntOp i32 }
          LocInfoE loc_21 ((LocInfoE loc_22 (use{IntOp i32} (LocInfoE loc_23 ("j")))) -{IntOp i32, IntOp i32} (LocInfoE loc_24 (i2v 1 i32))) ;
        locinfo: loc_11 ;
        Goto "#8"
      ]> $∅
    )%E
  |}.

  (* Definition of function [permut]. *)
  Definition impl_permut (global_copy_array global_list_new global_list_snoc global_next global_sort : loc): function := {|
    f_args := [
      ("A", void*);
      ("size", it_layout i32)
    ];
    f_local_vars := [
      ("copy", void*);
      ("l", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "l" <-{ PtrOp }
          LocInfoE loc_241 (Call (LocInfoE loc_243 (global_list_new)) [@{expr}  ]) ;
        locinfo: loc_237 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_237 ((LocInfoE loc_238 (use{IntOp i32} (LocInfoE loc_239 ("size")))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_240 (i2v 0 i32)))
        then
        locinfo: loc_233 ;
          Goto "#5"
        else
        locinfo: loc_181 ;
          Goto "#6"
      ]> $
      <[ "#1" :=
        locinfo: loc_181 ;
        expr: (LocInfoE loc_181 (Call (LocInfoE loc_227 (global_sort)) [@{expr} LocInfoE loc_228 (use{PtrOp} (LocInfoE loc_229 ("A"))) ;
        LocInfoE loc_230 (use{IntOp i32} (LocInfoE loc_231 ("size"))) ])) ;
        locinfo: loc_182 ;
        LocInfoE loc_218 ("copy") <-{ PtrOp }
          LocInfoE loc_219 (Call (LocInfoE loc_221 (global_copy_array)) [@{expr} LocInfoE loc_222 (use{PtrOp} (LocInfoE loc_223 ("A"))) ;
          LocInfoE loc_224 (use{IntOp i32} (LocInfoE loc_225 ("size"))) ]) ;
        locinfo: loc_183 ;
        expr: (LocInfoE loc_183 (Call (LocInfoE loc_213 (global_list_snoc)) [@{expr} LocInfoE loc_214 (&(LocInfoE loc_215 ("l"))) ;
        LocInfoE loc_216 (use{PtrOp} (LocInfoE loc_217 ("copy"))) ])) ;
        locinfo: loc_184 ;
        Goto "#2"
      ]> $
      <[ "#2" :=
        locinfo: loc_205 ;
        if{BoolOp, None}: LocInfoE loc_205 (Call (LocInfoE loc_207 (global_next)) [@{expr} LocInfoE loc_208 (use{PtrOp} (LocInfoE loc_209 ("A"))) ;
                          LocInfoE loc_210 (use{IntOp i32} (LocInfoE loc_211 ("size"))) ])
        then
        locinfo: loc_189 ;
          Goto "#3"
        else
        locinfo: loc_185 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_189 ;
        LocInfoE loc_197 ("copy") <-{ PtrOp }
          LocInfoE loc_198 (Call (LocInfoE loc_200 (global_copy_array)) [@{expr} LocInfoE loc_201 (use{PtrOp} (LocInfoE loc_202 ("A"))) ;
          LocInfoE loc_203 (use{IntOp i32} (LocInfoE loc_204 ("size"))) ]) ;
        locinfo: loc_190 ;
        expr: (LocInfoE loc_190 (Call (LocInfoE loc_192 (global_list_snoc)) [@{expr} LocInfoE loc_193 (&(LocInfoE loc_194 ("l"))) ;
        LocInfoE loc_195 (use{PtrOp} (LocInfoE loc_196 ("copy"))) ])) ;
        locinfo: loc_184 ;
        Goto "#2"
      ]> $
      <[ "#4" :=
        locinfo: loc_185 ;
        Return (LocInfoE loc_186 (use{PtrOp} (LocInfoE loc_187 ("l"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_233 ;
        Return (LocInfoE loc_234 (use{PtrOp} (LocInfoE loc_235 ("l"))))
      ]> $
      <[ "#6" :=
        locinfo: loc_181 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
