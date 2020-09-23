From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t09_switch.c]. *)
Section code.
  Definition file_0 : string := "tutorial/t09_switch.c".
  Definition loc_2 : location_info := LocationInfo file_0 7 2 7 12.
  Definition loc_3 : location_info := LocationInfo file_0 9 2 14 3.
  Definition loc_4 : location_info := LocationInfo file_0 16 2 16 11.
  Definition loc_5 : location_info := LocationInfo file_0 16 9 16 10.
  Definition loc_6 : location_info := LocationInfo file_0 16 9 16 10.
  Definition loc_7 : location_info := LocationInfo file_0 9 13 14 3.
  Definition loc_8 : location_info := LocationInfo file_0 9 14 10 14.
  Definition loc_10 : location_info := LocationInfo file_0 10 10 10 14.
  Definition loc_11 : location_info := LocationInfo file_0 10 14 11 14.
  Definition loc_13 : location_info := LocationInfo file_0 11 10 11 14.
  Definition loc_14 : location_info := LocationInfo file_0 11 14 12 14.
  Definition loc_16 : location_info := LocationInfo file_0 12 10 12 14.
  Definition loc_17 : location_info := LocationInfo file_0 12 14 13 14.
  Definition loc_19 : location_info := LocationInfo file_0 13 10 13 14.
  Definition loc_20 : location_info := LocationInfo file_0 13 10 13 11.
  Definition loc_21 : location_info := LocationInfo file_0 12 10 12 11.
  Definition loc_22 : location_info := LocationInfo file_0 11 10 11 11.
  Definition loc_23 : location_info := LocationInfo file_0 10 10 10 11.
  Definition loc_24 : location_info := LocationInfo file_0 9 10 9 11.
  Definition loc_25 : location_info := LocationInfo file_0 9 10 9 11.
  Definition loc_26 : location_info := LocationInfo file_0 7 10 7 11.
  Definition loc_27 : location_info := LocationInfo file_0 7 10 7 11.
  Definition loc_32 : location_info := LocationInfo file_0 24 2 24 12.
  Definition loc_33 : location_info := LocationInfo file_0 26 2 32 3.
  Definition loc_34 : location_info := LocationInfo file_0 34 2 34 11.
  Definition loc_35 : location_info := LocationInfo file_0 34 9 34 10.
  Definition loc_36 : location_info := LocationInfo file_0 34 9 34 10.
  Definition loc_37 : location_info := LocationInfo file_0 26 13 32 3.
  Definition loc_38 : location_info := LocationInfo file_0 26 14 27 14.
  Definition loc_40 : location_info := LocationInfo file_0 27 10 27 14.
  Definition loc_41 : location_info := LocationInfo file_0 27 14 28 14.
  Definition loc_43 : location_info := LocationInfo file_0 28 10 28 14.
  Definition loc_44 : location_info := LocationInfo file_0 28 14 29 14.
  Definition loc_46 : location_info := LocationInfo file_0 29 10 29 14.
  Definition loc_47 : location_info := LocationInfo file_0 29 14 30 14.
  Definition loc_49 : location_info := LocationInfo file_0 30 10 30 14.
  Definition loc_50 : location_info := LocationInfo file_0 30 14 31 15.
  Definition loc_52 : location_info := LocationInfo file_0 31 11 31 15.
  Definition loc_53 : location_info := LocationInfo file_0 31 11 31 12.
  Definition loc_54 : location_info := LocationInfo file_0 30 10 30 11.
  Definition loc_55 : location_info := LocationInfo file_0 29 10 29 11.
  Definition loc_56 : location_info := LocationInfo file_0 28 10 28 11.
  Definition loc_57 : location_info := LocationInfo file_0 27 10 27 11.
  Definition loc_58 : location_info := LocationInfo file_0 26 10 26 11.
  Definition loc_59 : location_info := LocationInfo file_0 26 10 26 11.
  Definition loc_60 : location_info := LocationInfo file_0 24 10 24 11.
  Definition loc_61 : location_info := LocationInfo file_0 24 10 24 11.
  Definition loc_66 : location_info := LocationInfo file_0 41 2 41 12.
  Definition loc_67 : location_info := LocationInfo file_0 43 2 49 3.
  Definition loc_68 : location_info := LocationInfo file_0 51 2 51 11.
  Definition loc_69 : location_info := LocationInfo file_0 51 9 51 10.
  Definition loc_70 : location_info := LocationInfo file_0 51 9 51 10.
  Definition loc_71 : location_info := LocationInfo file_0 43 13 49 3.
  Definition loc_72 : location_info := LocationInfo file_0 43 14 44 14.
  Definition loc_74 : location_info := LocationInfo file_0 44 10 44 14.
  Definition loc_75 : location_info := LocationInfo file_0 44 15 44 21.
  Definition loc_76 : location_info := LocationInfo file_0 44 21 45 14.
  Definition loc_78 : location_info := LocationInfo file_0 45 10 45 14.
  Definition loc_79 : location_info := LocationInfo file_0 45 15 45 21.
  Definition loc_80 : location_info := LocationInfo file_0 45 21 46 14.
  Definition loc_82 : location_info := LocationInfo file_0 46 10 46 14.
  Definition loc_83 : location_info := LocationInfo file_0 46 15 46 21.
  Definition loc_84 : location_info := LocationInfo file_0 46 21 47 14.
  Definition loc_86 : location_info := LocationInfo file_0 47 10 47 14.
  Definition loc_87 : location_info := LocationInfo file_0 47 15 47 21.
  Definition loc_88 : location_info := LocationInfo file_0 47 21 48 14.
  Definition loc_90 : location_info := LocationInfo file_0 48 10 48 14.
  Definition loc_91 : location_info := LocationInfo file_0 48 15 48 21.
  Definition loc_92 : location_info := LocationInfo file_0 48 10 48 11.
  Definition loc_93 : location_info := LocationInfo file_0 47 10 47 11.
  Definition loc_94 : location_info := LocationInfo file_0 46 10 46 11.
  Definition loc_95 : location_info := LocationInfo file_0 45 10 45 11.
  Definition loc_96 : location_info := LocationInfo file_0 44 10 44 11.
  Definition loc_97 : location_info := LocationInfo file_0 43 10 43 11.
  Definition loc_98 : location_info := LocationInfo file_0 43 10 43 11.
  Definition loc_99 : location_info := LocationInfo file_0 41 10 41 11.
  Definition loc_100 : location_info := LocationInfo file_0 41 10 41 11.
  Definition loc_105 : location_info := LocationInfo file_0 59 2 59 12.
  Definition loc_106 : location_info := LocationInfo file_0 61 2 61 22.
  Definition loc_107 : location_info := LocationInfo file_0 62 2 73 3.
  Definition loc_108 : location_info := LocationInfo file_0 75 2 75 11.
  Definition loc_109 : location_info := LocationInfo file_0 75 9 75 10.
  Definition loc_110 : location_info := LocationInfo file_0 75 9 75 10.
  Definition loc_111 : location_info := LocationInfo file_0 62 17 73 3.
  Definition loc_112 : location_info := LocationInfo file_0 62 18 72 26.
  Definition loc_114 : location_info := LocationInfo file_0 67 10 72 26.
  Definition loc_116 : location_info := LocationInfo file_0 67 10 72 26.
  Definition loc_117 : location_info := LocationInfo file_0 67 13 72 11.
  Definition loc_118 : location_info := LocationInfo file_0 67 15 67 19.
  Definition loc_119 : location_info := LocationInfo file_0 67 19 68 14.
  Definition loc_121 : location_info := LocationInfo file_0 68 10 68 14.
  Definition loc_122 : location_info := LocationInfo file_0 68 14 69 14.
  Definition loc_124 : location_info := LocationInfo file_0 69 10 69 14.
  Definition loc_125 : location_info := LocationInfo file_0 69 14 70 14.
  Definition loc_127 : location_info := LocationInfo file_0 70 10 70 14.
  Definition loc_128 : location_info := LocationInfo file_0 71 12 71 16.
  Definition loc_129 : location_info := LocationInfo file_0 67 10 72 26.
  Definition loc_130 : location_info := LocationInfo file_0 67 10 72 26.
  Definition loc_131 : location_info := LocationInfo file_0 71 14 71 15.
  Definition loc_132 : location_info := LocationInfo file_0 71 12 71 15.
  Definition loc_133 : location_info := LocationInfo file_0 71 14 71 15.
  Definition loc_134 : location_info := LocationInfo file_0 71 14 71 15.
  Definition loc_136 : location_info := LocationInfo file_0 70 10 70 11.
  Definition loc_137 : location_info := LocationInfo file_0 69 10 69 11.
  Definition loc_138 : location_info := LocationInfo file_0 68 10 68 11.
  Definition loc_139 : location_info := LocationInfo file_0 67 15 67 16.
  Definition loc_140 : location_info := LocationInfo file_0 72 19 72 24.
  Definition loc_141 : location_info := LocationInfo file_0 72 19 72 20.
  Definition loc_142 : location_info := LocationInfo file_0 72 19 72 20.
  Definition loc_143 : location_info := LocationInfo file_0 72 23 72 24.
  Definition loc_144 : location_info := LocationInfo file_0 62 10 62 15.
  Definition loc_145 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_146 : location_info := LocationInfo file_0 62 10 62 11.
  Definition loc_147 : location_info := LocationInfo file_0 62 14 62 15.
  Definition loc_148 : location_info := LocationInfo file_0 61 10 61 21.
  Definition loc_149 : location_info := LocationInfo file_0 61 10 61 17.
  Definition loc_150 : location_info := LocationInfo file_0 61 11 61 12.
  Definition loc_151 : location_info := LocationInfo file_0 61 11 61 12.
  Definition loc_152 : location_info := LocationInfo file_0 61 15 61 16.
  Definition loc_153 : location_info := LocationInfo file_0 61 20 61 21.
  Definition loc_156 : location_info := LocationInfo file_0 59 10 59 11.

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
        "o" <-{ it_layout i32 }
          LocInfoE loc_26 (use{it_layout i32} (LocInfoE loc_27 ("i"))) ;
        locinfo: loc_3 ;
        Switch i32
          (LocInfoE loc_24 (use{it_layout i32} (LocInfoE loc_25 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_8 ;
            Goto "#2") ::
            (locinfo: loc_11 ;
            Goto "#3") ::
            (locinfo: loc_14 ;
            Goto "#4") ::
            (locinfo: loc_17 ;
            Goto "#5") :: []
          )
          (locinfo: loc_4 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 (use{it_layout i32} (LocInfoE loc_6 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_10 ;
        LocInfoE loc_23 ("o") <-{ it_layout i32 }
          LocInfoE loc_10 ((LocInfoE loc_10 (use{it_layout i32} (LocInfoE loc_23 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_10 (i2v 1 i32))) ;
        locinfo: loc_11 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_13 ;
        LocInfoE loc_22 ("o") <-{ it_layout i32 }
          LocInfoE loc_13 ((LocInfoE loc_13 (use{it_layout i32} (LocInfoE loc_22 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_13 (i2v 1 i32))) ;
        locinfo: loc_14 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_16 ;
        LocInfoE loc_21 ("o") <-{ it_layout i32 }
          LocInfoE loc_16 ((LocInfoE loc_16 (use{it_layout i32} (LocInfoE loc_21 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_16 (i2v 1 i32))) ;
        locinfo: loc_17 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_19 ;
        LocInfoE loc_20 ("o") <-{ it_layout i32 }
          LocInfoE loc_19 ((LocInfoE loc_19 (use{it_layout i32} (LocInfoE loc_20 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (i2v 1 i32))) ;
        locinfo: loc_4 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_4 ;
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
        "o" <-{ it_layout i32 }
          LocInfoE loc_60 (use{it_layout i32} (LocInfoE loc_61 ("i"))) ;
        locinfo: loc_33 ;
        Switch i32
          (LocInfoE loc_58 (use{it_layout i32} (LocInfoE loc_59 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_38 ;
            Goto "#2") ::
            (locinfo: loc_41 ;
            Goto "#3") ::
            (locinfo: loc_44 ;
            Goto "#4") ::
            (locinfo: loc_47 ;
            Goto "#5") :: []
          )
          (locinfo: loc_50 ;
          Goto "#6")
      ]> $
      <[ "#1" :=
        locinfo: loc_34 ;
        Return (LocInfoE loc_35 (use{it_layout i32} (LocInfoE loc_36 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_40 ;
        LocInfoE loc_57 ("o") <-{ it_layout i32 }
          LocInfoE loc_40 ((LocInfoE loc_40 (use{it_layout i32} (LocInfoE loc_57 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_40 (i2v 1 i32))) ;
        locinfo: loc_41 ;
        Goto "#3"
      ]> $
      <[ "#3" :=
        locinfo: loc_43 ;
        LocInfoE loc_56 ("o") <-{ it_layout i32 }
          LocInfoE loc_43 ((LocInfoE loc_43 (use{it_layout i32} (LocInfoE loc_56 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_43 (i2v 1 i32))) ;
        locinfo: loc_44 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_46 ;
        LocInfoE loc_55 ("o") <-{ it_layout i32 }
          LocInfoE loc_46 ((LocInfoE loc_46 (use{it_layout i32} (LocInfoE loc_55 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_46 (i2v 1 i32))) ;
        locinfo: loc_47 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_49 ;
        LocInfoE loc_54 ("o") <-{ it_layout i32 }
          LocInfoE loc_49 ((LocInfoE loc_49 (use{it_layout i32} (LocInfoE loc_54 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_49 (i2v 1 i32))) ;
        locinfo: loc_50 ;
        Goto "#6"
      ]> $
      <[ "#6" :=
        locinfo: loc_52 ;
        LocInfoE loc_53 ("o") <-{ it_layout i32 }
          LocInfoE loc_52 ((LocInfoE loc_52 (use{it_layout i32} (LocInfoE loc_53 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_52 (i2v 1 i32))) ;
        locinfo: loc_34 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_34 ;
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
        "o" <-{ it_layout i32 }
          LocInfoE loc_99 (use{it_layout i32} (LocInfoE loc_100 ("i"))) ;
        locinfo: loc_67 ;
        Switch i32
          (LocInfoE loc_97 (use{it_layout i32} (LocInfoE loc_98 ("i"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> $
            <[ 4 := 4%nat ]> ∅
          )
          (
            (locinfo: loc_72 ;
            Goto "#2") ::
            (locinfo: loc_76 ;
            Goto "#3") ::
            (locinfo: loc_80 ;
            Goto "#4") ::
            (locinfo: loc_84 ;
            Goto "#5") ::
            (locinfo: loc_88 ;
            Goto "#6") :: []
          )
          (locinfo: loc_68 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (use{it_layout i32} (LocInfoE loc_70 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_74 ;
        LocInfoE loc_96 ("o") <-{ it_layout i32 }
          LocInfoE loc_74 ((LocInfoE loc_74 (use{it_layout i32} (LocInfoE loc_96 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_74 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_78 ;
        LocInfoE loc_95 ("o") <-{ it_layout i32 }
          LocInfoE loc_78 ((LocInfoE loc_78 (use{it_layout i32} (LocInfoE loc_95 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_78 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_82 ;
        LocInfoE loc_94 ("o") <-{ it_layout i32 }
          LocInfoE loc_82 ((LocInfoE loc_82 (use{it_layout i32} (LocInfoE loc_94 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_82 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        Goto "#1"
      ]> $
      <[ "#5" :=
        locinfo: loc_86 ;
        LocInfoE loc_93 ("o") <-{ it_layout i32 }
          LocInfoE loc_86 ((LocInfoE loc_86 (use{it_layout i32} (LocInfoE loc_93 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_86 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        Goto "#1"
      ]> $
      <[ "#6" :=
        locinfo: loc_90 ;
        LocInfoE loc_92 ("o") <-{ it_layout i32 }
          LocInfoE loc_90 ((LocInfoE loc_90 (use{it_layout i32} (LocInfoE loc_92 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_90 (i2v 1 i32))) ;
        locinfo: loc_68 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_68 ;
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
        "o" <-{ it_layout i32 } LocInfoE loc_156 (i2v 0 i32) ;
        "n" <-{ it_layout i32 }
          LocInfoE loc_148 ((LocInfoE loc_149 ((LocInfoE loc_150 (use{it_layout i32} (LocInfoE loc_151 ("i")))) +{IntOp i32, IntOp i32} (LocInfoE loc_152 (i2v 3 i32)))) /{IntOp i32, IntOp i32} (LocInfoE loc_153 (i2v 4 i32))) ;
        locinfo: loc_107 ;
        Switch i32
          (LocInfoE loc_144 ((LocInfoE loc_145 (use{it_layout i32} (LocInfoE loc_146 ("i")))) %{IntOp i32, IntOp i32} (LocInfoE loc_147 (i2v 4 i32))))
          (
            <[ 0 := 0%nat ]> $
            <[ 3 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 1 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_112 ;
            Goto "#2") ::
            (locinfo: loc_119 ;
            Goto "#3") ::
            (locinfo: loc_122 ;
            Goto "#4") ::
            (locinfo: loc_125 ;
            Goto "#8") :: []
          )
          (locinfo: loc_108 ;
          Goto "#1")
      ]> $
      <[ "#1" :=
        locinfo: loc_108 ;
        Return (LocInfoE loc_109 (use{it_layout i32} (LocInfoE loc_110 ("o"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_114 ;
        Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_121 ;
        LocInfoE loc_138 ("o") <-{ it_layout i32 }
          LocInfoE loc_121 ((LocInfoE loc_121 (use{it_layout i32} (LocInfoE loc_138 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_121 (i2v 1 i32))) ;
        locinfo: loc_122 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_124 ;
        LocInfoE loc_137 ("o") <-{ it_layout i32 }
          LocInfoE loc_124 ((LocInfoE loc_124 (use{it_layout i32} (LocInfoE loc_137 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_124 (i2v 1 i32))) ;
        locinfo: loc_125 ;
        Goto "#8"
      ]> $
      <[ "#5" :=
        locinfo: loc_140 ;
        if: LocInfoE loc_140 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_140 ((LocInfoE loc_141 (use{it_layout i32} (LocInfoE loc_142 ("n")))) >{IntOp i32, IntOp i32} (LocInfoE loc_143 (i2v 0 i32)))))
        then
        locinfo: loc_114 ;
          Goto "#6"
        else
        locinfo: loc_108 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_118 ;
        LocInfoE loc_139 ("o") <-{ it_layout i32 }
          LocInfoE loc_118 ((LocInfoE loc_118 (use{it_layout i32} (LocInfoE loc_139 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_118 (i2v 1 i32))) ;
        locinfo: loc_119 ;
        Goto "#3"
      ]> $
      <[ "#7" :=
        locinfo: loc_108 ;
        Goto "#1"
      ]> $
      <[ "#8" :=
        locinfo: loc_127 ;
        LocInfoE loc_136 ("o") <-{ it_layout i32 }
          LocInfoE loc_127 ((LocInfoE loc_127 (use{it_layout i32} (LocInfoE loc_136 ("o")))) +{IntOp i32, IntOp i32} (LocInfoE loc_127 (i2v 1 i32))) ;
        locinfo: loc_128 ;
        LocInfoE loc_131 ("n") <-{ it_layout i32 }
          LocInfoE loc_132 ((LocInfoE loc_133 (use{it_layout i32} (LocInfoE loc_134 ("n")))) -{IntOp i32, IntOp i32} (i2v 1 i32)) ;
        locinfo: loc_129 ;
        Goto "continue12"
      ]> $
      <[ "#9" :=
        locinfo: loc_108 ;
        Goto "#1"
      ]> $
      <[ "continue12" :=
        Goto "#5"
      ]> $∅
    )%E
  |}.
End code.
