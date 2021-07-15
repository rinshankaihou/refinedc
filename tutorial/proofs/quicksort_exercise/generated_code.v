From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_exercise.c]. *)
Section code.
  Definition file_0 : string := "tutorial/quicksort_exercise.c".
  Definition loc_2 : location_info := LocationInfo file_0 22 2 26 3.
  Definition loc_3 : location_info := LocationInfo file_0 22 27 24 3.
  Definition loc_4 : location_info := LocationInfo file_0 23 4 23 11.
  Definition loc_5 : location_info := LocationInfo file_0 23 4 23 6.
  Definition loc_6 : location_info := LocationInfo file_0 23 5 23 6.
  Definition loc_7 : location_info := LocationInfo file_0 23 5 23 6.
  Definition loc_8 : location_info := LocationInfo file_0 23 9 23 10.
  Definition loc_9 : location_info := LocationInfo file_0 23 9 23 10.
  Definition loc_10 : location_info := LocationInfo file_0 24 9 26 3.
  Definition loc_11 : location_info := LocationInfo file_0 25 4 25 27.
  Definition loc_12 : location_info := LocationInfo file_0 25 4 25 10.
  Definition loc_13 : location_info := LocationInfo file_0 25 4 25 10.
  Definition loc_14 : location_info := LocationInfo file_0 25 11 25 22.
  Definition loc_15 : location_info := LocationInfo file_0 25 12 25 22.
  Definition loc_16 : location_info := LocationInfo file_0 25 12 25 16.
  Definition loc_17 : location_info := LocationInfo file_0 25 12 25 16.
  Definition loc_18 : location_info := LocationInfo file_0 25 14 25 15.
  Definition loc_19 : location_info := LocationInfo file_0 25 14 25 15.
  Definition loc_20 : location_info := LocationInfo file_0 25 24 25 25.
  Definition loc_21 : location_info := LocationInfo file_0 25 24 25 25.
  Definition loc_22 : location_info := LocationInfo file_0 22 5 22 25.
  Definition loc_23 : location_info := LocationInfo file_0 22 5 22 7.
  Definition loc_24 : location_info := LocationInfo file_0 22 5 22 7.
  Definition loc_25 : location_info := LocationInfo file_0 22 6 22 7.
  Definition loc_26 : location_info := LocationInfo file_0 22 6 22 7.
  Definition loc_27 : location_info := LocationInfo file_0 22 11 22 25.
  Definition loc_30 : location_info := LocationInfo file_0 30 2 42 3.
  Definition loc_31 : location_info := LocationInfo file_0 30 27 32 3.
  Definition loc_32 : location_info := LocationInfo file_0 31 4 31 26.
  Definition loc_33 : location_info := LocationInfo file_0 31 11 31 25.
  Definition loc_34 : location_info := LocationInfo file_0 32 9 42 3.
  Definition loc_35 : location_info := LocationInfo file_0 33 4 33 48.
  Definition loc_36 : location_info := LocationInfo file_0 34 4 34 21.
  Definition loc_37 : location_info := LocationInfo file_0 35 4 41 5.
  Definition loc_38 : location_info := LocationInfo file_0 35 27 39 5.
  Definition loc_39 : location_info := LocationInfo file_0 36 6 36 22.
  Definition loc_40 : location_info := LocationInfo file_0 37 6 37 24.
  Definition loc_41 : location_info := LocationInfo file_0 38 6 38 18.
  Definition loc_42 : location_info := LocationInfo file_0 38 13 38 17.
  Definition loc_43 : location_info := LocationInfo file_0 38 13 38 17.
  Definition loc_44 : location_info := LocationInfo file_0 37 6 37 16.
  Definition loc_45 : location_info := LocationInfo file_0 37 6 37 10.
  Definition loc_46 : location_info := LocationInfo file_0 37 6 37 10.
  Definition loc_47 : location_info := LocationInfo file_0 37 19 37 23.
  Definition loc_48 : location_info := LocationInfo file_0 37 19 37 23.
  Definition loc_49 : location_info := LocationInfo file_0 36 6 36 8.
  Definition loc_50 : location_info := LocationInfo file_0 36 7 36 8.
  Definition loc_51 : location_info := LocationInfo file_0 36 7 36 8.
  Definition loc_52 : location_info := LocationInfo file_0 36 11 36 21.
  Definition loc_53 : location_info := LocationInfo file_0 36 11 36 21.
  Definition loc_54 : location_info := LocationInfo file_0 36 11 36 15.
  Definition loc_55 : location_info := LocationInfo file_0 36 11 36 15.
  Definition loc_56 : location_info := LocationInfo file_0 36 13 36 14.
  Definition loc_57 : location_info := LocationInfo file_0 36 13 36 14.
  Definition loc_58 : location_info := LocationInfo file_0 39 11 41 5.
  Definition loc_59 : location_info := LocationInfo file_0 40 6 40 18.
  Definition loc_60 : location_info := LocationInfo file_0 40 13 40 17.
  Definition loc_61 : location_info := LocationInfo file_0 40 13 40 17.
  Definition loc_62 : location_info := LocationInfo file_0 35 7 35 25.
  Definition loc_63 : location_info := LocationInfo file_0 35 7 35 12.
  Definition loc_64 : location_info := LocationInfo file_0 35 7 35 12.
  Definition loc_65 : location_info := LocationInfo file_0 35 16 35 25.
  Definition loc_66 : location_info := LocationInfo file_0 35 16 35 25.
  Definition loc_67 : location_info := LocationInfo file_0 35 16 35 20.
  Definition loc_68 : location_info := LocationInfo file_0 35 16 35 20.
  Definition loc_69 : location_info := LocationInfo file_0 35 18 35 19.
  Definition loc_70 : location_info := LocationInfo file_0 35 18 35 19.
  Definition loc_71 : location_info := LocationInfo file_0 34 18 34 20.
  Definition loc_72 : location_info := LocationInfo file_0 34 18 34 20.
  Definition loc_73 : location_info := LocationInfo file_0 34 19 34 20.
  Definition loc_74 : location_info := LocationInfo file_0 34 19 34 20.
  Definition loc_77 : location_info := LocationInfo file_0 33 18 33 47.
  Definition loc_78 : location_info := LocationInfo file_0 33 18 33 27.
  Definition loc_79 : location_info := LocationInfo file_0 33 18 33 27.
  Definition loc_80 : location_info := LocationInfo file_0 33 28 33 39.
  Definition loc_81 : location_info := LocationInfo file_0 33 29 33 39.
  Definition loc_82 : location_info := LocationInfo file_0 33 29 33 33.
  Definition loc_83 : location_info := LocationInfo file_0 33 29 33 33.
  Definition loc_84 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_85 : location_info := LocationInfo file_0 33 31 33 32.
  Definition loc_86 : location_info := LocationInfo file_0 33 41 33 46.
  Definition loc_87 : location_info := LocationInfo file_0 33 41 33 46.
  Definition loc_90 : location_info := LocationInfo file_0 30 5 30 25.
  Definition loc_91 : location_info := LocationInfo file_0 30 5 30 7.
  Definition loc_92 : location_info := LocationInfo file_0 30 5 30 7.
  Definition loc_93 : location_info := LocationInfo file_0 30 6 30 7.
  Definition loc_94 : location_info := LocationInfo file_0 30 6 30 7.
  Definition loc_95 : location_info := LocationInfo file_0 30 11 30 25.
  Definition loc_98 : location_info := LocationInfo file_0 46 2 54 3.
  Definition loc_99 : location_info := LocationInfo file_0 46 27 48 3.
  Definition loc_100 : location_info := LocationInfo file_0 47 4 47 11.
  Definition loc_102 : location_info := LocationInfo file_0 48 9 54 3.
  Definition loc_103 : location_info := LocationInfo file_0 49 4 49 26.
  Definition loc_104 : location_info := LocationInfo file_0 50 4 50 40.
  Definition loc_105 : location_info := LocationInfo file_0 51 4 51 23.
  Definition loc_106 : location_info := LocationInfo file_0 52 4 52 17.
  Definition loc_107 : location_info := LocationInfo file_0 53 4 53 22.
  Definition loc_108 : location_info := LocationInfo file_0 53 4 53 10.
  Definition loc_109 : location_info := LocationInfo file_0 53 4 53 10.
  Definition loc_110 : location_info := LocationInfo file_0 53 11 53 12.
  Definition loc_111 : location_info := LocationInfo file_0 53 11 53 12.
  Definition loc_112 : location_info := LocationInfo file_0 53 14 53 20.
  Definition loc_113 : location_info := LocationInfo file_0 53 14 53 20.
  Definition loc_114 : location_info := LocationInfo file_0 52 4 52 13.
  Definition loc_115 : location_info := LocationInfo file_0 52 4 52 13.
  Definition loc_116 : location_info := LocationInfo file_0 52 14 52 15.
  Definition loc_117 : location_info := LocationInfo file_0 52 14 52 15.
  Definition loc_118 : location_info := LocationInfo file_0 51 4 51 13.
  Definition loc_119 : location_info := LocationInfo file_0 51 4 51 13.
  Definition loc_120 : location_info := LocationInfo file_0 51 14 51 21.
  Definition loc_121 : location_info := LocationInfo file_0 51 15 51 21.
  Definition loc_122 : location_info := LocationInfo file_0 50 20 50 39.
  Definition loc_123 : location_info := LocationInfo file_0 50 20 50 29.
  Definition loc_124 : location_info := LocationInfo file_0 50 20 50 29.
  Definition loc_125 : location_info := LocationInfo file_0 50 30 50 31.
  Definition loc_126 : location_info := LocationInfo file_0 50 30 50 31.
  Definition loc_127 : location_info := LocationInfo file_0 50 33 50 38.
  Definition loc_128 : location_info := LocationInfo file_0 50 33 50 38.
  Definition loc_131 : location_info := LocationInfo file_0 49 16 49 25.
  Definition loc_132 : location_info := LocationInfo file_0 49 16 49 25.
  Definition loc_133 : location_info := LocationInfo file_0 49 16 49 20.
  Definition loc_134 : location_info := LocationInfo file_0 49 16 49 20.
  Definition loc_135 : location_info := LocationInfo file_0 49 18 49 19.
  Definition loc_136 : location_info := LocationInfo file_0 49 18 49 19.
  Definition loc_139 : location_info := LocationInfo file_0 46 5 46 25.
  Definition loc_140 : location_info := LocationInfo file_0 46 5 46 7.
  Definition loc_141 : location_info := LocationInfo file_0 46 5 46 7.
  Definition loc_142 : location_info := LocationInfo file_0 46 6 46 7.
  Definition loc_143 : location_info := LocationInfo file_0 46 6 46 7.
  Definition loc_144 : location_info := LocationInfo file_0 46 11 46 25.

  (* Definition of struct [list_node]. *)
  Program Definition struct_list_node := {|
    sl_members := [
      (Some "val", it_layout i32);
      (None, Layout 4%nat 0%nat);
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [append]. *)
  Definition impl_append (global_append : loc): function := {|
    f_args := [
      ("l", void*);
      ("k", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_22 ;
        if: LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((LocInfoE loc_23 (use{PtrOp} (LocInfoE loc_25 (!{PtrOp} (LocInfoE loc_26 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_27 (NULL)))))
        then
        locinfo: loc_4 ;
          Goto "#1"
        else
        locinfo: loc_11 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_4 ;
        LocInfoE loc_6 (!{PtrOp} (LocInfoE loc_7 ("l"))) <-{ PtrOp }
          LocInfoE loc_8 (use{PtrOp} (LocInfoE loc_9 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        expr: (LocInfoE loc_11 (Call (LocInfoE loc_13 (global_append)) [@{expr} LocInfoE loc_14 (&(LocInfoE loc_15 ((LocInfoE loc_16 (!{PtrOp} (LocInfoE loc_18 (!{PtrOp} (LocInfoE loc_19 ("l")))))) at{struct_list_node} "next"))) ;
        LocInfoE loc_20 (use{PtrOp} (LocInfoE loc_21 ("k"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [partition]. *)
  Definition impl_partition (global_partition : loc): function := {|
    f_args := [
      ("l", void*);
      ("pivot", it_layout i32)
    ];
    f_local_vars := [
      ("rest", void*);
      ("head", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_90 ;
        if: LocInfoE loc_90 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_90 ((LocInfoE loc_91 (use{PtrOp} (LocInfoE loc_93 (!{PtrOp} (LocInfoE loc_94 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_95 (NULL)))))
        then
        locinfo: loc_32 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_32 ;
        Return (LocInfoE loc_33 (NULL))
      ]> $
      <[ "#2" :=
        "rest" <-{ PtrOp }
          LocInfoE loc_77 (Call (LocInfoE loc_79 (global_partition)) [@{expr} LocInfoE loc_80 (&(LocInfoE loc_81 ((LocInfoE loc_82 (!{PtrOp} (LocInfoE loc_84 (!{PtrOp} (LocInfoE loc_85 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_86 (use{IntOp i32} (LocInfoE loc_87 ("pivot"))) ]) ;
        "head" <-{ PtrOp }
          LocInfoE loc_71 (use{PtrOp} (LocInfoE loc_73 (!{PtrOp} (LocInfoE loc_74 ("l"))))) ;
        locinfo: loc_62 ;
        if: LocInfoE loc_62 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_62 ((LocInfoE loc_63 (use{IntOp i32} (LocInfoE loc_64 ("pivot")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_65 (use{IntOp i32} (LocInfoE loc_66 ((LocInfoE loc_67 (!{PtrOp} (LocInfoE loc_69 (!{PtrOp} (LocInfoE loc_70 ("l")))))) at{struct_list_node} "val")))))))
        then
        locinfo: loc_39 ;
          Goto "#3"
        else
        locinfo: loc_59 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_39 ;
        LocInfoE loc_50 (!{PtrOp} (LocInfoE loc_51 ("l"))) <-{ PtrOp }
          LocInfoE loc_52 (use{PtrOp} (LocInfoE loc_53 ((LocInfoE loc_54 (!{PtrOp} (LocInfoE loc_56 (!{PtrOp} (LocInfoE loc_57 ("l")))))) at{struct_list_node} "next"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_44 ((LocInfoE loc_45 (!{PtrOp} (LocInfoE loc_46 ("head")))) at{struct_list_node} "next") <-{ PtrOp }
          LocInfoE loc_47 (use{PtrOp} (LocInfoE loc_48 ("rest"))) ;
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{PtrOp} (LocInfoE loc_43 ("head"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (use{PtrOp} (LocInfoE loc_61 ("rest"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [quicksort]. *)
  Definition impl_quicksort (global_append global_partition global_quicksort : loc): function := {|
    f_args := [
      ("l", void*)
    ];
    f_local_vars := [
      ("pivot", it_layout i32);
      ("higher", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_139 ;
        if: LocInfoE loc_139 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_139 ((LocInfoE loc_140 (use{PtrOp} (LocInfoE loc_142 (!{PtrOp} (LocInfoE loc_143 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_144 (NULL)))))
        then
        locinfo: loc_100 ;
          Goto "#1"
        else
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_100 ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        "pivot" <-{ IntOp i32 }
          LocInfoE loc_131 (use{IntOp i32} (LocInfoE loc_132 ((LocInfoE loc_133 (!{PtrOp} (LocInfoE loc_135 (!{PtrOp} (LocInfoE loc_136 ("l")))))) at{struct_list_node} "val"))) ;
        "higher" <-{ PtrOp }
          LocInfoE loc_122 (Call (LocInfoE loc_124 (global_partition)) [@{expr} LocInfoE loc_125 (use{PtrOp} (LocInfoE loc_126 ("l"))) ;
          LocInfoE loc_127 (use{IntOp i32} (LocInfoE loc_128 ("pivot"))) ]) ;
        locinfo: loc_105 ;
        expr: (LocInfoE loc_105 (Call (LocInfoE loc_119 (global_quicksort)) [@{expr} LocInfoE loc_120 (&(LocInfoE loc_121 ("higher"))) ])) ;
        locinfo: loc_106 ;
        expr: (LocInfoE loc_106 (Call (LocInfoE loc_115 (global_quicksort)) [@{expr} LocInfoE loc_116 (use{PtrOp} (LocInfoE loc_117 ("l"))) ])) ;
        locinfo: loc_107 ;
        expr: (LocInfoE loc_107 (Call (LocInfoE loc_109 (global_append)) [@{expr} LocInfoE loc_110 (use{PtrOp} (LocInfoE loc_111 ("l"))) ;
        LocInfoE loc_112 (use{PtrOp} (LocInfoE loc_113 ("higher"))) ])) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
