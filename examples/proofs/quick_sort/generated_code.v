From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/quick_sort.c]. *)
Section code.
  Definition file_0 : string := "examples/quick_sort.c".
  Definition loc_2 : location_info := LocationInfo file_0 32 2 32 13.
  Definition loc_3 : location_info := LocationInfo file_0 33 2 33 13.
  Definition loc_4 : location_info := LocationInfo file_0 34 2 34 19.
  Definition loc_5 : location_info := LocationInfo file_0 38 2 55 3.
  Definition loc_6 : location_info := LocationInfo file_0 57 2 57 15.
  Definition loc_7 : location_info := LocationInfo file_0 58 2 58 11.
  Definition loc_8 : location_info := LocationInfo file_0 58 9 58 10.
  Definition loc_9 : location_info := LocationInfo file_0 58 9 58 10.
  Definition loc_10 : location_info := LocationInfo file_0 57 2 57 8.
  Definition loc_11 : location_info := LocationInfo file_0 57 2 57 8.
  Definition loc_12 : location_info := LocationInfo file_0 57 2 57 5.
  Definition loc_13 : location_info := LocationInfo file_0 57 2 57 5.
  Definition loc_14 : location_info := LocationInfo file_0 57 6 57 7.
  Definition loc_15 : location_info := LocationInfo file_0 57 6 57 7.
  Definition loc_16 : location_info := LocationInfo file_0 57 11 57 14.
  Definition loc_17 : location_info := LocationInfo file_0 57 11 57 14.
  Definition loc_18 : location_info := LocationInfo file_0 38 2 55 3.
  Definition loc_19 : location_info := LocationInfo file_0 39 2 55 3.
  Definition loc_20 : location_info := LocationInfo file_0 42 4 45 5.
  Definition loc_21 : location_info := LocationInfo file_0 46 4 46 20.
  Definition loc_22 : location_info := LocationInfo file_0 50 4 53 5.
  Definition loc_23 : location_info := LocationInfo file_0 54 4 54 20.
  Definition loc_24 : location_info := LocationInfo file_0 38 2 55 3.
  Definition loc_25 : location_info := LocationInfo file_0 38 2 55 3.
  Definition loc_26 : location_info := LocationInfo file_0 54 4 54 10.
  Definition loc_27 : location_info := LocationInfo file_0 54 4 54 10.
  Definition loc_28 : location_info := LocationInfo file_0 54 4 54 7.
  Definition loc_29 : location_info := LocationInfo file_0 54 4 54 7.
  Definition loc_30 : location_info := LocationInfo file_0 54 8 54 9.
  Definition loc_31 : location_info := LocationInfo file_0 54 8 54 9.
  Definition loc_32 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_33 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_34 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_35 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_36 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_37 : location_info := LocationInfo file_0 54 17 54 18.
  Definition loc_38 : location_info := LocationInfo file_0 54 17 54 18.
  Definition loc_39 : location_info := LocationInfo file_0 50 4 53 5.
  Definition loc_40 : location_info := LocationInfo file_0 51 4 53 5.
  Definition loc_41 : location_info := LocationInfo file_0 52 8 52 12.
  Definition loc_42 : location_info := LocationInfo file_0 50 4 53 5.
  Definition loc_43 : location_info := LocationInfo file_0 50 4 53 5.
  Definition loc_44 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_45 : location_info := LocationInfo file_0 52 8 52 11.
  Definition loc_46 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_47 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_50 : location_info := LocationInfo file_0 50 11 50 16.
  Definition loc_51 : location_info := LocationInfo file_0 50 11 50 12.
  Definition loc_52 : location_info := LocationInfo file_0 50 11 50 12.
  Definition loc_53 : location_info := LocationInfo file_0 50 15 50 16.
  Definition loc_54 : location_info := LocationInfo file_0 50 15 50 16.
  Definition loc_55 : location_info := LocationInfo file_0 50 20 50 33.
  Definition loc_56 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_57 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_58 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_59 : location_info := LocationInfo file_0 50 20 50 23.
  Definition loc_60 : location_info := LocationInfo file_0 50 20 50 23.
  Definition loc_61 : location_info := LocationInfo file_0 50 24 50 25.
  Definition loc_62 : location_info := LocationInfo file_0 50 24 50 25.
  Definition loc_63 : location_info := LocationInfo file_0 50 30 50 33.
  Definition loc_64 : location_info := LocationInfo file_0 50 30 50 33.
  Definition loc_65 : location_info := LocationInfo file_0 46 4 46 10.
  Definition loc_66 : location_info := LocationInfo file_0 46 4 46 10.
  Definition loc_67 : location_info := LocationInfo file_0 46 4 46 7.
  Definition loc_68 : location_info := LocationInfo file_0 46 4 46 7.
  Definition loc_69 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_70 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_71 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_72 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_73 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_74 : location_info := LocationInfo file_0 46 13 46 16.
  Definition loc_75 : location_info := LocationInfo file_0 46 13 46 16.
  Definition loc_76 : location_info := LocationInfo file_0 46 17 46 18.
  Definition loc_77 : location_info := LocationInfo file_0 46 17 46 18.
  Definition loc_78 : location_info := LocationInfo file_0 42 4 45 5.
  Definition loc_79 : location_info := LocationInfo file_0 43 4 45 5.
  Definition loc_80 : location_info := LocationInfo file_0 44 8 44 12.
  Definition loc_81 : location_info := LocationInfo file_0 42 4 45 5.
  Definition loc_82 : location_info := LocationInfo file_0 42 4 45 5.
  Definition loc_83 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_84 : location_info := LocationInfo file_0 44 8 44 11.
  Definition loc_85 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_86 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_89 : location_info := LocationInfo file_0 42 11 42 16.
  Definition loc_90 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_91 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_92 : location_info := LocationInfo file_0 42 15 42 16.
  Definition loc_93 : location_info := LocationInfo file_0 42 15 42 16.
  Definition loc_94 : location_info := LocationInfo file_0 42 20 42 33.
  Definition loc_95 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_96 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_97 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_98 : location_info := LocationInfo file_0 42 20 42 23.
  Definition loc_99 : location_info := LocationInfo file_0 42 20 42 23.
  Definition loc_100 : location_info := LocationInfo file_0 42 24 42 25.
  Definition loc_101 : location_info := LocationInfo file_0 42 24 42 25.
  Definition loc_102 : location_info := LocationInfo file_0 42 30 42 33.
  Definition loc_103 : location_info := LocationInfo file_0 42 30 42 33.
  Definition loc_104 : location_info := LocationInfo file_0 38 9 38 14.
  Definition loc_105 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_106 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_107 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_108 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_109 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_110 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_111 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_112 : location_info := LocationInfo file_0 34 12 34 15.
  Definition loc_113 : location_info := LocationInfo file_0 34 12 34 15.
  Definition loc_114 : location_info := LocationInfo file_0 34 16 34 17.
  Definition loc_115 : location_info := LocationInfo file_0 34 16 34 17.
  Definition loc_118 : location_info := LocationInfo file_0 33 10 33 12.
  Definition loc_119 : location_info := LocationInfo file_0 33 10 33 12.
  Definition loc_122 : location_info := LocationInfo file_0 32 10 32 12.
  Definition loc_123 : location_info := LocationInfo file_0 32 10 32 12.
  Definition loc_128 : location_info := LocationInfo file_0 76 2 81 3.
  Definition loc_129 : location_info := LocationInfo file_0 77 2 81 3.
  Definition loc_130 : location_info := LocationInfo file_0 78 6 78 37.
  Definition loc_131 : location_info := LocationInfo file_0 79 6 79 28.
  Definition loc_132 : location_info := LocationInfo file_0 80 6 80 28.
  Definition loc_133 : location_info := LocationInfo file_0 80 6 80 11.
  Definition loc_134 : location_info := LocationInfo file_0 80 6 80 11.
  Definition loc_135 : location_info := LocationInfo file_0 80 12 80 15.
  Definition loc_136 : location_info := LocationInfo file_0 80 12 80 15.
  Definition loc_137 : location_info := LocationInfo file_0 80 17 80 22.
  Definition loc_138 : location_info := LocationInfo file_0 80 17 80 18.
  Definition loc_139 : location_info := LocationInfo file_0 80 17 80 18.
  Definition loc_140 : location_info := LocationInfo file_0 80 21 80 22.
  Definition loc_141 : location_info := LocationInfo file_0 80 24 80 26.
  Definition loc_142 : location_info := LocationInfo file_0 80 24 80 26.
  Definition loc_143 : location_info := LocationInfo file_0 79 6 79 11.
  Definition loc_144 : location_info := LocationInfo file_0 79 6 79 11.
  Definition loc_145 : location_info := LocationInfo file_0 79 12 79 15.
  Definition loc_146 : location_info := LocationInfo file_0 79 12 79 15.
  Definition loc_147 : location_info := LocationInfo file_0 79 17 79 19.
  Definition loc_148 : location_info := LocationInfo file_0 79 17 79 19.
  Definition loc_149 : location_info := LocationInfo file_0 79 21 79 26.
  Definition loc_150 : location_info := LocationInfo file_0 79 21 79 22.
  Definition loc_151 : location_info := LocationInfo file_0 79 21 79 22.
  Definition loc_152 : location_info := LocationInfo file_0 79 25 79 26.
  Definition loc_153 : location_info := LocationInfo file_0 78 14 78 36.
  Definition loc_154 : location_info := LocationInfo file_0 78 14 78 23.
  Definition loc_155 : location_info := LocationInfo file_0 78 14 78 23.
  Definition loc_156 : location_info := LocationInfo file_0 78 24 78 27.
  Definition loc_157 : location_info := LocationInfo file_0 78 24 78 27.
  Definition loc_158 : location_info := LocationInfo file_0 78 29 78 31.
  Definition loc_159 : location_info := LocationInfo file_0 78 29 78 31.
  Definition loc_160 : location_info := LocationInfo file_0 78 33 78 35.
  Definition loc_161 : location_info := LocationInfo file_0 78 33 78 35.
  Definition loc_165 : location_info := LocationInfo file_0 76 6 76 13.
  Definition loc_166 : location_info := LocationInfo file_0 76 6 76 8.
  Definition loc_167 : location_info := LocationInfo file_0 76 6 76 8.
  Definition loc_168 : location_info := LocationInfo file_0 76 11 76 13.
  Definition loc_169 : location_info := LocationInfo file_0 76 11 76 13.

  (* Definition of function [partition]. *)
  Definition impl_partition : function := {|
    f_args := [
      ("arr", void*);
      ("lo", it_layout i32);
      ("hi", it_layout i32)
    ];
    f_local_vars := [
      ("i", it_layout i32);
      ("key", it_layout i32);
      ("j", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "i" <-{ it_layout i32 }
          LocInfoE loc_122 (use{it_layout i32} (LocInfoE loc_123 ("lo"))) ;
        "j" <-{ it_layout i32 }
          LocInfoE loc_118 (use{it_layout i32} (LocInfoE loc_119 ("hi"))) ;
        "key" <-{ it_layout i32 }
          LocInfoE loc_109 (use{it_layout i32} (LocInfoE loc_111 ((LocInfoE loc_112 (!{void*} (LocInfoE loc_113 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_114 (use{it_layout i32} (LocInfoE loc_115 ("i"))))))) ;
        locinfo: loc_5 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_104 ;
        if: LocInfoE loc_104 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_104 ((LocInfoE loc_105 (use{it_layout i32} (LocInfoE loc_106 ("i")))) <{IntOp i32, IntOp i32} (LocInfoE loc_107 (use{it_layout i32} (LocInfoE loc_108 ("j")))))))
        then
        locinfo: loc_20 ;
          Goto "#2"
        else
        locinfo: loc_6 ;
          Goto "#3"
      ]> $
      <[ "#10" :=
        locinfo: loc_55 ;
        if: LocInfoE loc_55 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_55 ((LocInfoE loc_56 (use{it_layout i32} (LocInfoE loc_58 ((LocInfoE loc_59 (!{void*} (LocInfoE loc_60 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_61 (use{it_layout i32} (LocInfoE loc_62 ("i")))))))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_63 (use{it_layout i32} (LocInfoE loc_64 ("key")))))))
        then
        locinfo: loc_41 ;
          Goto "#8"
        else
        locinfo: loc_23 ;
          Goto "#9"
      ]> $
      <[ "#11" :=
        locinfo: loc_94 ;
        if: LocInfoE loc_94 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_94 ((LocInfoE loc_95 (use{it_layout i32} (LocInfoE loc_97 ((LocInfoE loc_98 (!{void*} (LocInfoE loc_99 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_100 (use{it_layout i32} (LocInfoE loc_101 ("j")))))))) ≥{IntOp i32, IntOp i32} (LocInfoE loc_102 (use{it_layout i32} (LocInfoE loc_103 ("key")))))))
        then
        locinfo: loc_80 ;
          Goto "#5"
        else
        locinfo: loc_21 ;
          Goto "#6"
      ]> $
      <[ "#2" :=
        locinfo: loc_20 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_6 ;
        LocInfoE loc_11 ((LocInfoE loc_12 (!{void*} (LocInfoE loc_13 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_14 (use{it_layout i32} (LocInfoE loc_15 ("i"))))) <-{ it_layout i32 }
          LocInfoE loc_16 (use{it_layout i32} (LocInfoE loc_17 ("key"))) ;
        locinfo: loc_7 ;
        Return (LocInfoE loc_8 (use{it_layout i32} (LocInfoE loc_9 ("i"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_89 ;
        if: LocInfoE loc_89 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_89 ((LocInfoE loc_90 (use{it_layout i32} (LocInfoE loc_91 ("i")))) <{IntOp i32, IntOp i32} (LocInfoE loc_92 (use{it_layout i32} (LocInfoE loc_93 ("j")))))))
        then
        Goto "#11"
        else
        locinfo: loc_21 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_80 ;
        LocInfoE loc_83 ("j") <-{ it_layout i32 }
          LocInfoE loc_84 ((LocInfoE loc_85 (use{it_layout i32} (LocInfoE loc_86 ("j")))) -{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_81 ;
        Goto "continue4"
      ]> $
      <[ "#6" :=
        locinfo: loc_21 ;
        LocInfoE loc_66 ((LocInfoE loc_67 (!{void*} (LocInfoE loc_68 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_69 (use{it_layout i32} (LocInfoE loc_70 ("i"))))) <-{ it_layout i32 }
          LocInfoE loc_71 (use{it_layout i32} (LocInfoE loc_73 ((LocInfoE loc_74 (!{void*} (LocInfoE loc_75 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_76 (use{it_layout i32} (LocInfoE loc_77 ("j"))))))) ;
        locinfo: loc_22 ;
        Goto "#7"
      ]> $
      <[ "#7" :=
        locinfo: loc_50 ;
        if: LocInfoE loc_50 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_50 ((LocInfoE loc_51 (use{it_layout i32} (LocInfoE loc_52 ("i")))) <{IntOp i32, IntOp i32} (LocInfoE loc_53 (use{it_layout i32} (LocInfoE loc_54 ("j")))))))
        then
        Goto "#10"
        else
        locinfo: loc_23 ;
          Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_41 ;
        LocInfoE loc_44 ("i") <-{ it_layout i32 }
          LocInfoE loc_45 ((LocInfoE loc_46 (use{it_layout i32} (LocInfoE loc_47 ("i")))) +{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_42 ;
        Goto "continue6"
      ]> $
      <[ "#9" :=
        locinfo: loc_23 ;
        LocInfoE loc_27 ((LocInfoE loc_28 (!{void*} (LocInfoE loc_29 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_30 (use{it_layout i32} (LocInfoE loc_31 ("j"))))) <-{ it_layout i32 }
          LocInfoE loc_32 (use{it_layout i32} (LocInfoE loc_34 ((LocInfoE loc_35 (!{void*} (LocInfoE loc_36 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_37 (use{it_layout i32} (LocInfoE loc_38 ("i"))))))) ;
        locinfo: loc_24 ;
        Goto "continue2"
      ]> $
      <[ "continue2" :=
        locinfo: loc_5 ;
        Goto "#1"
      ]> $
      <[ "continue4" :=
        locinfo: loc_20 ;
        Goto "#4"
      ]> $
      <[ "continue6" :=
        locinfo: loc_22 ;
        Goto "#7"
      ]> $∅
    )%E
  |}.

  (* Definition of function [qsort]. *)
  Definition impl_qsort (global_partition global_qsort : loc): function := {|
    f_args := [
      ("arr", void*);
      ("lo", it_layout i32);
      ("hi", it_layout i32)
    ];
    f_local_vars := [
      ("k", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_165 ;
        if: LocInfoE loc_165 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_165 ((LocInfoE loc_166 (use{it_layout i32} (LocInfoE loc_167 ("lo")))) <{IntOp i32, IntOp i32} (LocInfoE loc_168 (use{it_layout i32} (LocInfoE loc_169 ("hi")))))))
        then
        Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        "k" <-{ it_layout i32 }
          LocInfoE loc_153 (Call (LocInfoE loc_155 (global_partition)) [@{expr} LocInfoE loc_156 (use{void*} (LocInfoE loc_157 ("arr"))) ;
          LocInfoE loc_158 (use{it_layout i32} (LocInfoE loc_159 ("lo"))) ;
          LocInfoE loc_160 (use{it_layout i32} (LocInfoE loc_161 ("hi"))) ]) ;
        locinfo: loc_131 ;
        expr: (LocInfoE loc_131 (Call (LocInfoE loc_144 (global_qsort)) [@{expr} LocInfoE loc_145 (use{void*} (LocInfoE loc_146 ("arr"))) ;
        LocInfoE loc_147 (use{it_layout i32} (LocInfoE loc_148 ("lo"))) ;
        LocInfoE loc_149 ((LocInfoE loc_150 (use{it_layout i32} (LocInfoE loc_151 ("k")))) -{IntOp i32, IntOp i32} (LocInfoE loc_152 (i2v 1 i32))) ])) ;
        locinfo: loc_132 ;
        expr: (LocInfoE loc_132 (Call (LocInfoE loc_134 (global_qsort)) [@{expr} LocInfoE loc_135 (use{void*} (LocInfoE loc_136 ("arr"))) ;
        LocInfoE loc_137 ((LocInfoE loc_138 (use{it_layout i32} (LocInfoE loc_139 ("k")))) +{IntOp i32, IntOp i32} (LocInfoE loc_140 (i2v 1 i32))) ;
        LocInfoE loc_141 (use{it_layout i32} (LocInfoE loc_142 ("hi"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
