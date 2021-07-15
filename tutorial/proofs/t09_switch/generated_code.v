From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t09_switch.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 7 2 7 12.
  Definition loc_12 : location_info := LocationInfo file_1 9 2 14 3.
  Definition loc_13 : location_info := LocationInfo file_1 16 2 16 11.
  Definition loc_14 : location_info := LocationInfo file_1 16 9 16 10.
  Definition loc_15 : location_info := LocationInfo file_1 16 9 16 10.
  Definition loc_16 : location_info := LocationInfo file_1 9 13 14 3.
  Definition loc_17 : location_info := LocationInfo file_1 9 14 10 14.
  Definition loc_19 : location_info := LocationInfo file_1 10 10 10 14.
  Definition loc_20 : location_info := LocationInfo file_1 10 14 11 14.
  Definition loc_22 : location_info := LocationInfo file_1 11 10 11 14.
  Definition loc_23 : location_info := LocationInfo file_1 11 14 12 14.
  Definition loc_25 : location_info := LocationInfo file_1 12 10 12 14.
  Definition loc_26 : location_info := LocationInfo file_1 12 14 13 14.
  Definition loc_28 : location_info := LocationInfo file_1 13 10 13 14.
  Definition loc_29 : location_info := LocationInfo file_1 13 10 13 11.
  Definition loc_30 : location_info := LocationInfo file_1 12 10 12 11.
  Definition loc_31 : location_info := LocationInfo file_1 11 10 11 11.
  Definition loc_32 : location_info := LocationInfo file_1 10 10 10 11.
  Definition loc_33 : location_info := LocationInfo file_1 9 10 9 11.
  Definition loc_34 : location_info := LocationInfo file_1 9 10 9 11.
  Definition loc_35 : location_info := LocationInfo file_1 7 10 7 11.
  Definition loc_36 : location_info := LocationInfo file_1 7 10 7 11.
  Definition loc_41 : location_info := LocationInfo file_1 24 2 24 12.
  Definition loc_42 : location_info := LocationInfo file_1 26 2 32 3.
  Definition loc_43 : location_info := LocationInfo file_1 34 2 34 11.
  Definition loc_44 : location_info := LocationInfo file_1 34 9 34 10.
  Definition loc_45 : location_info := LocationInfo file_1 34 9 34 10.
  Definition loc_46 : location_info := LocationInfo file_1 26 13 32 3.
  Definition loc_47 : location_info := LocationInfo file_1 26 14 27 14.
  Definition loc_49 : location_info := LocationInfo file_1 27 10 27 14.
  Definition loc_50 : location_info := LocationInfo file_1 27 14 28 14.
  Definition loc_52 : location_info := LocationInfo file_1 28 10 28 14.
  Definition loc_53 : location_info := LocationInfo file_1 28 14 29 14.
  Definition loc_55 : location_info := LocationInfo file_1 29 10 29 14.
  Definition loc_56 : location_info := LocationInfo file_1 29 14 30 14.
  Definition loc_58 : location_info := LocationInfo file_1 30 10 30 14.
  Definition loc_59 : location_info := LocationInfo file_1 30 14 31 15.
  Definition loc_61 : location_info := LocationInfo file_1 31 11 31 15.
  Definition loc_62 : location_info := LocationInfo file_1 31 11 31 12.
  Definition loc_63 : location_info := LocationInfo file_1 30 10 30 11.
  Definition loc_64 : location_info := LocationInfo file_1 29 10 29 11.
  Definition loc_65 : location_info := LocationInfo file_1 28 10 28 11.
  Definition loc_66 : location_info := LocationInfo file_1 27 10 27 11.
  Definition loc_67 : location_info := LocationInfo file_1 26 10 26 11.
  Definition loc_68 : location_info := LocationInfo file_1 26 10 26 11.
  Definition loc_69 : location_info := LocationInfo file_1 24 10 24 11.
  Definition loc_70 : location_info := LocationInfo file_1 24 10 24 11.
  Definition loc_75 : location_info := LocationInfo file_1 41 2 41 12.
  Definition loc_76 : location_info := LocationInfo file_1 43 2 49 3.
  Definition loc_77 : location_info := LocationInfo file_1 51 2 51 11.
  Definition loc_78 : location_info := LocationInfo file_1 51 9 51 10.
  Definition loc_79 : location_info := LocationInfo file_1 51 9 51 10.
  Definition loc_80 : location_info := LocationInfo file_1 43 13 49 3.
  Definition loc_81 : location_info := LocationInfo file_1 43 14 44 14.
  Definition loc_83 : location_info := LocationInfo file_1 44 10 44 14.
  Definition loc_84 : location_info := LocationInfo file_1 44 15 44 21.
  Definition loc_85 : location_info := LocationInfo file_1 44 21 45 14.
  Definition loc_87 : location_info := LocationInfo file_1 45 10 45 14.
  Definition loc_88 : location_info := LocationInfo file_1 45 15 45 21.
  Definition loc_89 : location_info := LocationInfo file_1 45 21 46 14.
  Definition loc_91 : location_info := LocationInfo file_1 46 10 46 14.
  Definition loc_92 : location_info := LocationInfo file_1 46 15 46 21.
  Definition loc_93 : location_info := LocationInfo file_1 46 21 47 14.
  Definition loc_95 : location_info := LocationInfo file_1 47 10 47 14.
  Definition loc_96 : location_info := LocationInfo file_1 47 15 47 21.
  Definition loc_97 : location_info := LocationInfo file_1 47 21 48 14.
  Definition loc_99 : location_info := LocationInfo file_1 48 10 48 14.
  Definition loc_100 : location_info := LocationInfo file_1 48 15 48 21.
  Definition loc_101 : location_info := LocationInfo file_1 48 10 48 11.
  Definition loc_102 : location_info := LocationInfo file_1 47 10 47 11.
  Definition loc_103 : location_info := LocationInfo file_1 46 10 46 11.
  Definition loc_104 : location_info := LocationInfo file_1 45 10 45 11.
  Definition loc_105 : location_info := LocationInfo file_1 44 10 44 11.
  Definition loc_106 : location_info := LocationInfo file_1 43 10 43 11.
  Definition loc_107 : location_info := LocationInfo file_1 43 10 43 11.
  Definition loc_108 : location_info := LocationInfo file_1 41 10 41 11.
  Definition loc_109 : location_info := LocationInfo file_1 41 10 41 11.
  Definition loc_114 : location_info := LocationInfo file_1 59 2 59 12.
  Definition loc_115 : location_info := LocationInfo file_1 61 2 61 22.
  Definition loc_116 : location_info := LocationInfo file_1 62 2 73 3.
  Definition loc_117 : location_info := LocationInfo file_1 75 2 75 11.
  Definition loc_118 : location_info := LocationInfo file_1 75 9 75 10.
  Definition loc_119 : location_info := LocationInfo file_1 75 9 75 10.
  Definition loc_120 : location_info := LocationInfo file_1 62 17 73 3.
  Definition loc_121 : location_info := LocationInfo file_1 62 18 72 26.
  Definition loc_123 : location_info := LocationInfo file_1 67 10 72 26.
  Definition loc_125 : location_info := LocationInfo file_1 67 10 72 26.
  Definition loc_126 : location_info := LocationInfo file_1 67 13 72 11.
  Definition loc_127 : location_info := LocationInfo file_1 67 15 67 19.
  Definition loc_128 : location_info := LocationInfo file_1 67 19 68 14.
  Definition loc_130 : location_info := LocationInfo file_1 68 10 68 14.
  Definition loc_131 : location_info := LocationInfo file_1 68 14 69 14.
  Definition loc_133 : location_info := LocationInfo file_1 69 10 69 14.
  Definition loc_134 : location_info := LocationInfo file_1 69 14 70 14.
  Definition loc_136 : location_info := LocationInfo file_1 70 10 70 14.
  Definition loc_137 : location_info := LocationInfo file_1 71 12 71 16.
  Definition loc_138 : location_info := LocationInfo file_1 67 10 72 26.
  Definition loc_139 : location_info := LocationInfo file_1 67 10 72 26.
  Definition loc_140 : location_info := LocationInfo file_1 71 14 71 15.
  Definition loc_141 : location_info := LocationInfo file_1 71 12 71 15.
  Definition loc_142 : location_info := LocationInfo file_1 71 14 71 15.
  Definition loc_143 : location_info := LocationInfo file_1 71 14 71 15.
  Definition loc_145 : location_info := LocationInfo file_1 70 10 70 11.
  Definition loc_146 : location_info := LocationInfo file_1 69 10 69 11.
  Definition loc_147 : location_info := LocationInfo file_1 68 10 68 11.
  Definition loc_148 : location_info := LocationInfo file_1 67 15 67 16.
  Definition loc_149 : location_info := LocationInfo file_1 72 19 72 24.
  Definition loc_150 : location_info := LocationInfo file_1 72 19 72 20.
  Definition loc_151 : location_info := LocationInfo file_1 72 19 72 20.
  Definition loc_152 : location_info := LocationInfo file_1 72 23 72 24.
  Definition loc_153 : location_info := LocationInfo file_1 62 10 62 15.
  Definition loc_154 : location_info := LocationInfo file_1 62 10 62 11.
  Definition loc_155 : location_info := LocationInfo file_1 62 10 62 11.
  Definition loc_156 : location_info := LocationInfo file_1 62 14 62 15.
  Definition loc_157 : location_info := LocationInfo file_1 61 10 61 21.
  Definition loc_158 : location_info := LocationInfo file_1 61 10 61 17.
  Definition loc_159 : location_info := LocationInfo file_1 61 11 61 12.
  Definition loc_160 : location_info := LocationInfo file_1 61 11 61 12.
  Definition loc_161 : location_info := LocationInfo file_1 61 15 61 16.
  Definition loc_162 : location_info := LocationInfo file_1 61 20 61 21.
  Definition loc_165 : location_info := LocationInfo file_1 59 10 59 11.

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

  (* Definition of function [test_switch]. *)
  Definition impl_test_switch : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
      ("o", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "o" <-{ IntOp i32 }
          LocInfoE loc_35 (use{IntOp i32} (LocInfoE loc_36 ("i"))) ;
        locinfo: loc_12 ;
        Switch i32
          (LocInfoE loc_33 (use{IntOp i32} (LocInfoE loc_34 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_17 ;
            Goto "#2") ::
            (locinfo: loc_20 ;
            Goto "#3") ::
            (locinfo: loc_23 ;
            Goto "#4") ::
            (locinfo: loc_26 ;
            Goto "#5") :: []
          )
          (locinfo: loc_13 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (use{IntOp i32} (LocInfoE loc_15 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_19 ;
        LocInfoE loc_32 ("o") <-{ IntOp i32 }
          LocInfoE loc_19 ((LocInfoE loc_19 (use{IntOp i32} (LocInfoE loc_32 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (i2v 1 i32))) ;
        locinfo: loc_20 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_22 ;
        LocInfoE loc_31 ("o") <-{ IntOp i32 }
          LocInfoE loc_22 ((LocInfoE loc_22 (use{IntOp i32} (LocInfoE loc_31 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_22 (i2v 1 i32))) ;
        locinfo: loc_23 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_25 ;
        LocInfoE loc_30 ("o") <-{ IntOp i32 }
          LocInfoE loc_25 ((LocInfoE loc_25 (use{IntOp i32} (LocInfoE loc_30 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_25 (i2v 1 i32))) ;
        locinfo: loc_26 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_28 ;
        LocInfoE loc_29 ("o") <-{ IntOp i32 }
          LocInfoE loc_28 ((LocInfoE loc_28 (use{IntOp i32} (LocInfoE loc_29 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_28 (i2v 1 i32))) ;
        locinfo: loc_13 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_13 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [test_switch_default]. *)
  Definition impl_test_switch_default : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
      ("o", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "o" <-{ IntOp i32 }
          LocInfoE loc_69 (use{IntOp i32} (LocInfoE loc_70 ("i"))) ;
        locinfo: loc_42 ;
        Switch i32
          (LocInfoE loc_67 (use{IntOp i32} (LocInfoE loc_68 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_47 ;
            Goto "#2") ::
            (locinfo: loc_50 ;
            Goto "#3") ::
            (locinfo: loc_53 ;
            Goto "#4") ::
            (locinfo: loc_56 ;
            Goto "#5") :: []
          )
          (locinfo: loc_59 ;
          Goto "#6")
      ]> $
      <[ "#1" :=
        locinfo: loc_43 ;
        Return (LocInfoE loc_44 (use{IntOp i32} (LocInfoE loc_45 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_49 ;
        LocInfoE loc_66 ("o") <-{ IntOp i32 }
          LocInfoE loc_49 ((LocInfoE loc_49 (use{IntOp i32} (LocInfoE loc_66 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_49 (i2v 1 i32))) ;
        locinfo: loc_50 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_52 ;
        LocInfoE loc_65 ("o") <-{ IntOp i32 }
          LocInfoE loc_52 ((LocInfoE loc_52 (use{IntOp i32} (LocInfoE loc_65 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_52 (i2v 1 i32))) ;
        locinfo: loc_53 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_55 ;
        LocInfoE loc_64 ("o") <-{ IntOp i32 }
          LocInfoE loc_55 ((LocInfoE loc_55 (use{IntOp i32} (LocInfoE loc_64 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_55 (i2v 1 i32))) ;
        locinfo: loc_56 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_58 ;
        LocInfoE loc_63 ("o") <-{ IntOp i32 }
          LocInfoE loc_58 ((LocInfoE loc_58 (use{IntOp i32} (LocInfoE loc_63 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_58 (i2v 1 i32))) ;
        locinfo: loc_59 ;
        Goto "#6"
      ]> $
      <[ "#6" :=
        locinfo: loc_61 ;
        LocInfoE loc_62 ("o") <-{ IntOp i32 }
          LocInfoE loc_61 ((LocInfoE loc_61 (use{IntOp i32} (LocInfoE loc_62 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_61 (i2v 1 i32))) ;
        locinfo: loc_43 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_43 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [incr_less_than_5]. *)
  Definition impl_incr_less_than_5 : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
      ("o", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "o" <-{ IntOp i32 }
          LocInfoE loc_108 (use{IntOp i32} (LocInfoE loc_109 ("i"))) ;
        locinfo: loc_76 ;
        Switch i32
          (LocInfoE loc_106 (use{IntOp i32} (LocInfoE loc_107 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> $
            <[ 4 := 4%nat ]> ∅
          )
          (
            (locinfo: loc_81 ;
            Goto "#2") ::
            (locinfo: loc_85 ;
            Goto "#3") ::
            (locinfo: loc_89 ;
            Goto "#4") ::
            (locinfo: loc_93 ;
            Goto "#5") ::
            (locinfo: loc_97 ;
            Goto "#6") :: []
          )
          (locinfo: loc_77 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_77 ;
        Return (LocInfoE loc_78 (use{IntOp i32} (LocInfoE loc_79 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_83 ;
        LocInfoE loc_105 ("o") <-{ IntOp i32 }
          LocInfoE loc_83 ((LocInfoE loc_83 (use{IntOp i32} (LocInfoE loc_105 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_83 (i2v 1 i32))) ;
        locinfo: loc_77 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_87 ;
        LocInfoE loc_104 ("o") <-{ IntOp i32 }
          LocInfoE loc_87 ((LocInfoE loc_87 (use{IntOp i32} (LocInfoE loc_104 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_87 (i2v 1 i32))) ;
        locinfo: loc_77 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_91 ;
        LocInfoE loc_103 ("o") <-{ IntOp i32 }
          LocInfoE loc_91 ((LocInfoE loc_91 (use{IntOp i32} (LocInfoE loc_103 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_91 (i2v 1 i32))) ;
        locinfo: loc_77 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_95 ;
        LocInfoE loc_102 ("o") <-{ IntOp i32 }
          LocInfoE loc_95 ((LocInfoE loc_95 (use{IntOp i32} (LocInfoE loc_102 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_95 (i2v 1 i32))) ;
        locinfo: loc_77 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_99 ;
        LocInfoE loc_101 ("o") <-{ IntOp i32 }
          LocInfoE loc_99 ((LocInfoE loc_99 (use{IntOp i32} (LocInfoE loc_101 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_99 (i2v 1 i32))) ;
        locinfo: loc_77 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_77 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [duffs_identity]. *)
  Definition impl_duffs_identity : function := {|
    f_args := [
      ("i", it_layout i32)
    ];
    f_local_vars := [
      ("o", it_layout i32);
      ("n", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "o" <-{ IntOp i32 } LocInfoE loc_165 (i2v 0 i32) ;
        "n" <-{ IntOp i32 }
          LocInfoE loc_157 ((LocInfoE loc_158 ((LocInfoE loc_159 (use{IntOp i32} (LocInfoE loc_160 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_161 (i2v 3 i32)))) /{IntOp i32, IntOp i32} (LocInfoE loc_162 (i2v 4 i32))) ;
        locinfo: loc_116 ;
        Switch i32
          (LocInfoE loc_153 ((LocInfoE loc_154 (use{IntOp i32} (LocInfoE loc_155 ("i")))) %{IntOp i32, IntOp i32} (LocInfoE loc_156 (i2v 4 i32))))
          (
            <[ 0 := 0%nat ]> $
            <[ 3 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 1 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_121 ;
            Goto "#2") ::
            (locinfo: loc_128 ;
            Goto "#3") ::
            (locinfo: loc_131 ;
            Goto "#4") ::
            (locinfo: loc_134 ;
            Goto "#8") :: []
          )
          (locinfo: loc_117 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_117 ;
        Return (LocInfoE loc_118 (use{IntOp i32} (LocInfoE loc_119 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_123 ;
        Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_130 ;
        LocInfoE loc_147 ("o") <-{ IntOp i32 }
          LocInfoE loc_130 ((LocInfoE loc_130 (use{IntOp i32} (LocInfoE loc_147 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_130 (i2v 1 i32))) ;
        locinfo: loc_131 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_133 ;
        LocInfoE loc_146 ("o") <-{ IntOp i32 }
          LocInfoE loc_133 ((LocInfoE loc_133 (use{IntOp i32} (LocInfoE loc_146 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_133 (i2v 1 i32))) ;
        locinfo: loc_134 ;
        Goto "#8"
      ]> $
      <[ "#5" :=
        locinfo: loc_149 ;
        if: LocInfoE loc_149 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_149 ((LocInfoE loc_150 (use{IntOp i32} (LocInfoE loc_151 ("n")))) >{IntOp i32, IntOp i32} (LocInfoE loc_152 (i2v 0 i32)))))
        then
        locinfo: loc_123 ;
          Goto "#6"
        else
        locinfo: loc_117 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_127 ;
        LocInfoE loc_148 ("o") <-{ IntOp i32 }
          LocInfoE loc_127 ((LocInfoE loc_127 (use{IntOp i32} (LocInfoE loc_148 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_127 (i2v 1 i32))) ;
        locinfo: loc_128 ;
        Goto "#3"
      ]> $
      <[ "#7" :=
        locinfo: loc_117 ;
        Goto "#1"
      ]> $
      <[ "#8" :=
        locinfo: loc_136 ;
        LocInfoE loc_145 ("o") <-{ IntOp i32 }
          LocInfoE loc_136 ((LocInfoE loc_136 (use{IntOp i32} (LocInfoE loc_145 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_136 (i2v 1 i32))) ;
        locinfo: loc_137 ;
        LocInfoE loc_140 ("n") <-{ IntOp i32 }
          LocInfoE loc_141 ((LocInfoE loc_142 (use{IntOp i32} (LocInfoE loc_143 ("n")))) -{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_138 ;
        Goto "continue14"
      ]> $
      <[ "#9" :=
        locinfo: loc_117 ;
        Goto "#1"
      ]> $
      <[ "continue14" :=
        Goto "#5"
      ]> $∅
    )%E
  |}.
End code.
