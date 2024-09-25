From caesium Require Export notation.
From caesium Require Import tactics.
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
  Definition loc_18 : location_info := LocationInfo file_0 39 2 55 3.
  Definition loc_19 : location_info := LocationInfo file_0 42 4 45 5.
  Definition loc_20 : location_info := LocationInfo file_0 46 4 46 20.
  Definition loc_21 : location_info := LocationInfo file_0 50 4 53 5.
  Definition loc_22 : location_info := LocationInfo file_0 54 4 54 20.
  Definition loc_23 : location_info := LocationInfo file_0 54 4 54 10.
  Definition loc_24 : location_info := LocationInfo file_0 54 4 54 10.
  Definition loc_25 : location_info := LocationInfo file_0 54 4 54 7.
  Definition loc_26 : location_info := LocationInfo file_0 54 4 54 7.
  Definition loc_27 : location_info := LocationInfo file_0 54 8 54 9.
  Definition loc_28 : location_info := LocationInfo file_0 54 8 54 9.
  Definition loc_29 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_30 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_31 : location_info := LocationInfo file_0 54 13 54 19.
  Definition loc_32 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_33 : location_info := LocationInfo file_0 54 13 54 16.
  Definition loc_34 : location_info := LocationInfo file_0 54 17 54 18.
  Definition loc_35 : location_info := LocationInfo file_0 54 17 54 18.
  Definition loc_36 : location_info := LocationInfo file_0 51 4 53 5.
  Definition loc_37 : location_info := LocationInfo file_0 52 8 52 12.
  Definition loc_38 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_39 : location_info := LocationInfo file_0 52 8 52 11.
  Definition loc_40 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_41 : location_info := LocationInfo file_0 52 10 52 11.
  Definition loc_43 : location_info := LocationInfo file_0 50 11 50 33.
  Definition loc_44 : location_info := LocationInfo file_0 50 11 50 16.
  Definition loc_45 : location_info := LocationInfo file_0 50 11 50 12.
  Definition loc_46 : location_info := LocationInfo file_0 50 11 50 12.
  Definition loc_47 : location_info := LocationInfo file_0 50 15 50 16.
  Definition loc_48 : location_info := LocationInfo file_0 50 15 50 16.
  Definition loc_49 : location_info := LocationInfo file_0 50 20 50 33.
  Definition loc_50 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_51 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_52 : location_info := LocationInfo file_0 50 20 50 26.
  Definition loc_53 : location_info := LocationInfo file_0 50 20 50 23.
  Definition loc_54 : location_info := LocationInfo file_0 50 20 50 23.
  Definition loc_55 : location_info := LocationInfo file_0 50 24 50 25.
  Definition loc_56 : location_info := LocationInfo file_0 50 24 50 25.
  Definition loc_57 : location_info := LocationInfo file_0 50 30 50 33.
  Definition loc_58 : location_info := LocationInfo file_0 50 30 50 33.
  Definition loc_59 : location_info := LocationInfo file_0 46 4 46 10.
  Definition loc_60 : location_info := LocationInfo file_0 46 4 46 10.
  Definition loc_61 : location_info := LocationInfo file_0 46 4 46 7.
  Definition loc_62 : location_info := LocationInfo file_0 46 4 46 7.
  Definition loc_63 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_64 : location_info := LocationInfo file_0 46 8 46 9.
  Definition loc_65 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_66 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_67 : location_info := LocationInfo file_0 46 13 46 19.
  Definition loc_68 : location_info := LocationInfo file_0 46 13 46 16.
  Definition loc_69 : location_info := LocationInfo file_0 46 13 46 16.
  Definition loc_70 : location_info := LocationInfo file_0 46 17 46 18.
  Definition loc_71 : location_info := LocationInfo file_0 46 17 46 18.
  Definition loc_72 : location_info := LocationInfo file_0 43 4 45 5.
  Definition loc_73 : location_info := LocationInfo file_0 44 8 44 12.
  Definition loc_74 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_75 : location_info := LocationInfo file_0 44 8 44 11.
  Definition loc_76 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_77 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_79 : location_info := LocationInfo file_0 42 11 42 33.
  Definition loc_80 : location_info := LocationInfo file_0 42 11 42 16.
  Definition loc_81 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_82 : location_info := LocationInfo file_0 42 11 42 12.
  Definition loc_83 : location_info := LocationInfo file_0 42 15 42 16.
  Definition loc_84 : location_info := LocationInfo file_0 42 15 42 16.
  Definition loc_85 : location_info := LocationInfo file_0 42 20 42 33.
  Definition loc_86 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_87 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_88 : location_info := LocationInfo file_0 42 20 42 26.
  Definition loc_89 : location_info := LocationInfo file_0 42 20 42 23.
  Definition loc_90 : location_info := LocationInfo file_0 42 20 42 23.
  Definition loc_91 : location_info := LocationInfo file_0 42 24 42 25.
  Definition loc_92 : location_info := LocationInfo file_0 42 24 42 25.
  Definition loc_93 : location_info := LocationInfo file_0 42 30 42 33.
  Definition loc_94 : location_info := LocationInfo file_0 42 30 42 33.
  Definition loc_95 : location_info := LocationInfo file_0 38 9 38 14.
  Definition loc_96 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_97 : location_info := LocationInfo file_0 38 9 38 10.
  Definition loc_98 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_99 : location_info := LocationInfo file_0 38 13 38 14.
  Definition loc_100 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_101 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_102 : location_info := LocationInfo file_0 34 12 34 18.
  Definition loc_103 : location_info := LocationInfo file_0 34 12 34 15.
  Definition loc_104 : location_info := LocationInfo file_0 34 12 34 15.
  Definition loc_105 : location_info := LocationInfo file_0 34 16 34 17.
  Definition loc_106 : location_info := LocationInfo file_0 34 16 34 17.
  Definition loc_109 : location_info := LocationInfo file_0 33 10 33 12.
  Definition loc_110 : location_info := LocationInfo file_0 33 10 33 12.
  Definition loc_113 : location_info := LocationInfo file_0 32 10 32 12.
  Definition loc_114 : location_info := LocationInfo file_0 32 10 32 12.
  Definition loc_119 : location_info := LocationInfo file_0 76 2 81 3.
  Definition loc_120 : location_info := LocationInfo file_0 77 2 81 3.
  Definition loc_121 : location_info := LocationInfo file_0 78 6 78 37.
  Definition loc_122 : location_info := LocationInfo file_0 79 6 79 28.
  Definition loc_123 : location_info := LocationInfo file_0 80 6 80 28.
  Definition loc_124 : location_info := LocationInfo file_0 80 6 80 11.
  Definition loc_125 : location_info := LocationInfo file_0 80 6 80 11.
  Definition loc_126 : location_info := LocationInfo file_0 80 12 80 15.
  Definition loc_127 : location_info := LocationInfo file_0 80 12 80 15.
  Definition loc_128 : location_info := LocationInfo file_0 80 17 80 22.
  Definition loc_129 : location_info := LocationInfo file_0 80 17 80 18.
  Definition loc_130 : location_info := LocationInfo file_0 80 17 80 18.
  Definition loc_131 : location_info := LocationInfo file_0 80 21 80 22.
  Definition loc_132 : location_info := LocationInfo file_0 80 24 80 26.
  Definition loc_133 : location_info := LocationInfo file_0 80 24 80 26.
  Definition loc_134 : location_info := LocationInfo file_0 79 6 79 11.
  Definition loc_135 : location_info := LocationInfo file_0 79 6 79 11.
  Definition loc_136 : location_info := LocationInfo file_0 79 12 79 15.
  Definition loc_137 : location_info := LocationInfo file_0 79 12 79 15.
  Definition loc_138 : location_info := LocationInfo file_0 79 17 79 19.
  Definition loc_139 : location_info := LocationInfo file_0 79 17 79 19.
  Definition loc_140 : location_info := LocationInfo file_0 79 21 79 26.
  Definition loc_141 : location_info := LocationInfo file_0 79 21 79 22.
  Definition loc_142 : location_info := LocationInfo file_0 79 21 79 22.
  Definition loc_143 : location_info := LocationInfo file_0 79 25 79 26.
  Definition loc_144 : location_info := LocationInfo file_0 78 14 78 36.
  Definition loc_145 : location_info := LocationInfo file_0 78 14 78 23.
  Definition loc_146 : location_info := LocationInfo file_0 78 14 78 23.
  Definition loc_147 : location_info := LocationInfo file_0 78 24 78 27.
  Definition loc_148 : location_info := LocationInfo file_0 78 24 78 27.
  Definition loc_149 : location_info := LocationInfo file_0 78 29 78 31.
  Definition loc_150 : location_info := LocationInfo file_0 78 29 78 31.
  Definition loc_151 : location_info := LocationInfo file_0 78 33 78 35.
  Definition loc_152 : location_info := LocationInfo file_0 78 33 78 35.
  Definition loc_155 : location_info := LocationInfo file_0 76 2 81 3.
  Definition loc_156 : location_info := LocationInfo file_0 76 6 76 13.
  Definition loc_157 : location_info := LocationInfo file_0 76 6 76 8.
  Definition loc_158 : location_info := LocationInfo file_0 76 6 76 8.
  Definition loc_159 : location_info := LocationInfo file_0 76 11 76 13.
  Definition loc_160 : location_info := LocationInfo file_0 76 11 76 13.

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
        "i" <-{ IntOp i32 }
          LocInfoE loc_113 (use{IntOp i32} (LocInfoE loc_114 ("lo"))) ;
        "j" <-{ IntOp i32 }
          LocInfoE loc_109 (use{IntOp i32} (LocInfoE loc_110 ("hi"))) ;
        "key" <-{ IntOp i32 }
          LocInfoE loc_100 (use{IntOp i32} (LocInfoE loc_102 ((LocInfoE loc_103 (!{PtrOp} (LocInfoE loc_104 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_105 (use{IntOp i32} (LocInfoE loc_106 ("i"))))))) ;
        locinfo: loc_5 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_95 ;
        if{IntOp i32, None}: LocInfoE loc_95 ((LocInfoE loc_96 (use{IntOp i32} (LocInfoE loc_97 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_98 (use{IntOp i32} (LocInfoE loc_99 ("j")))))
        then
        locinfo: loc_19 ;
          Goto "#2"
        else
        locinfo: loc_6 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_19 ;
        Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_6 ;
        LocInfoE loc_11 ((LocInfoE loc_12 (!{PtrOp} (LocInfoE loc_13 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_14 (use{IntOp i32} (LocInfoE loc_15 ("i"))))) <-{ IntOp i32 }
          LocInfoE loc_16 (use{IntOp i32} (LocInfoE loc_17 ("key"))) ;
        locinfo: loc_7 ;
        Return (LocInfoE loc_8 (use{IntOp i32} (LocInfoE loc_9 ("i"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_79 ;
        if{IntOp i32, None}: LocInfoE loc_79 ((LocInfoE loc_80 ((LocInfoE loc_81 (use{IntOp i32} (LocInfoE loc_82 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_83 (use{IntOp i32} (LocInfoE loc_84 ("j")))))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_85 ((LocInfoE loc_86 (use{IntOp i32} (LocInfoE loc_88 ((LocInfoE loc_89 (!{PtrOp} (LocInfoE loc_90 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_91 (use{IntOp i32} (LocInfoE loc_92 ("j")))))))) ≥{IntOp i32, IntOp i32, i32} (LocInfoE loc_93 (use{IntOp i32} (LocInfoE loc_94 ("key")))))))
        then
        locinfo: loc_73 ;
          Goto "#5"
        else
        locinfo: loc_20 ;
          Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_73 ;
        LocInfoE loc_74 ("j") <-{ IntOp i32 }
          LocInfoE loc_75 ((LocInfoE loc_76 (use{IntOp i32} (LocInfoE loc_77 ("j")))) -{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_19 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        locinfo: loc_20 ;
        LocInfoE loc_60 ((LocInfoE loc_61 (!{PtrOp} (LocInfoE loc_62 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_63 (use{IntOp i32} (LocInfoE loc_64 ("i"))))) <-{ IntOp i32 }
          LocInfoE loc_65 (use{IntOp i32} (LocInfoE loc_67 ((LocInfoE loc_68 (!{PtrOp} (LocInfoE loc_69 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_70 (use{IntOp i32} (LocInfoE loc_71 ("j"))))))) ;
        locinfo: loc_21 ;
        Goto "#7"
      ]> $
      <[ "#7" :=
        locinfo: loc_43 ;
        if{IntOp i32, None}: LocInfoE loc_43 ((LocInfoE loc_44 ((LocInfoE loc_45 (use{IntOp i32} (LocInfoE loc_46 ("i")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_47 (use{IntOp i32} (LocInfoE loc_48 ("j")))))) &&{IntOp i32, IntOp i32, i32} (LocInfoE loc_49 ((LocInfoE loc_50 (use{IntOp i32} (LocInfoE loc_52 ((LocInfoE loc_53 (!{PtrOp} (LocInfoE loc_54 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_55 (use{IntOp i32} (LocInfoE loc_56 ("i")))))))) ≤{IntOp i32, IntOp i32, i32} (LocInfoE loc_57 (use{IntOp i32} (LocInfoE loc_58 ("key")))))))
        then
        locinfo: loc_37 ;
          Goto "#8"
        else
        locinfo: loc_22 ;
          Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_37 ;
        LocInfoE loc_38 ("i") <-{ IntOp i32 }
          LocInfoE loc_39 ((LocInfoE loc_40 (use{IntOp i32} (LocInfoE loc_41 ("i")))) +{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_21 ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_22 ;
        LocInfoE loc_24 ((LocInfoE loc_25 (!{PtrOp} (LocInfoE loc_26 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_27 (use{IntOp i32} (LocInfoE loc_28 ("j"))))) <-{ IntOp i32 }
          LocInfoE loc_29 (use{IntOp i32} (LocInfoE loc_31 ((LocInfoE loc_32 (!{PtrOp} (LocInfoE loc_33 ("arr")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_34 (use{IntOp i32} (LocInfoE loc_35 ("i"))))))) ;
        locinfo: loc_5 ;
        Goto "#1"
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
        locinfo: loc_156 ;
        if{IntOp i32, None}: LocInfoE loc_156 ((LocInfoE loc_157 (use{IntOp i32} (LocInfoE loc_158 ("lo")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_159 (use{IntOp i32} (LocInfoE loc_160 ("hi")))))
        then
        Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        "k" <-{ IntOp i32 }
          LocInfoE loc_144 (Call (LocInfoE loc_146 (global_partition)) [@{expr} LocInfoE loc_147 (use{PtrOp} (LocInfoE loc_148 ("arr"))) ;
          LocInfoE loc_149 (use{IntOp i32} (LocInfoE loc_150 ("lo"))) ;
          LocInfoE loc_151 (use{IntOp i32} (LocInfoE loc_152 ("hi"))) ]) ;
        locinfo: loc_122 ;
        expr: (LocInfoE loc_122 (Call (LocInfoE loc_135 (global_qsort)) [@{expr} LocInfoE loc_136 (use{PtrOp} (LocInfoE loc_137 ("arr"))) ;
        LocInfoE loc_138 (use{IntOp i32} (LocInfoE loc_139 ("lo"))) ;
        LocInfoE loc_140 ((LocInfoE loc_141 (use{IntOp i32} (LocInfoE loc_142 ("k")))) -{IntOp i32, IntOp i32} (LocInfoE loc_143 (i2v 1 i32))) ])) ;
        locinfo: loc_123 ;
        expr: (LocInfoE loc_123 (Call (LocInfoE loc_125 (global_qsort)) [@{expr} LocInfoE loc_126 (use{PtrOp} (LocInfoE loc_127 ("arr"))) ;
        LocInfoE loc_128 ((LocInfoE loc_129 (use{IntOp i32} (LocInfoE loc_130 ("k")))) +{IntOp i32, IntOp i32} (LocInfoE loc_131 (i2v 1 i32))) ;
        LocInfoE loc_132 (use{IntOp i32} (LocInfoE loc_133 ("hi"))) ])) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
