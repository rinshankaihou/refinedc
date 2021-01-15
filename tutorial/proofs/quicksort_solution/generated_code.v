From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/quicksort_solution.c]. *)
Section code.
  Definition file_0 : string := "tutorial/quicksort_solution.c".
  Definition loc_2 : location_info := LocationInfo file_0 26 2 30 3.
  Definition loc_3 : location_info := LocationInfo file_0 26 27 28 3.
  Definition loc_4 : location_info := LocationInfo file_0 27 4 27 11.
  Definition loc_5 : location_info := LocationInfo file_0 27 4 27 6.
  Definition loc_6 : location_info := LocationInfo file_0 27 5 27 6.
  Definition loc_7 : location_info := LocationInfo file_0 27 5 27 6.
  Definition loc_8 : location_info := LocationInfo file_0 27 9 27 10.
  Definition loc_9 : location_info := LocationInfo file_0 27 9 27 10.
  Definition loc_10 : location_info := LocationInfo file_0 28 9 30 3.
  Definition loc_11 : location_info := LocationInfo file_0 29 4 29 27.
  Definition loc_12 : location_info := LocationInfo file_0 29 4 29 10.
  Definition loc_13 : location_info := LocationInfo file_0 29 4 29 10.
  Definition loc_14 : location_info := LocationInfo file_0 29 11 29 22.
  Definition loc_15 : location_info := LocationInfo file_0 29 12 29 22.
  Definition loc_16 : location_info := LocationInfo file_0 29 12 29 16.
  Definition loc_17 : location_info := LocationInfo file_0 29 12 29 16.
  Definition loc_18 : location_info := LocationInfo file_0 29 14 29 15.
  Definition loc_19 : location_info := LocationInfo file_0 29 14 29 15.
  Definition loc_20 : location_info := LocationInfo file_0 29 24 29 25.
  Definition loc_21 : location_info := LocationInfo file_0 29 24 29 25.
  Definition loc_22 : location_info := LocationInfo file_0 26 5 26 25.
  Definition loc_23 : location_info := LocationInfo file_0 26 5 26 7.
  Definition loc_24 : location_info := LocationInfo file_0 26 5 26 7.
  Definition loc_25 : location_info := LocationInfo file_0 26 6 26 7.
  Definition loc_26 : location_info := LocationInfo file_0 26 6 26 7.
  Definition loc_27 : location_info := LocationInfo file_0 26 11 26 25.
  Definition loc_30 : location_info := LocationInfo file_0 41 2 53 3.
  Definition loc_31 : location_info := LocationInfo file_0 41 27 43 3.
  Definition loc_32 : location_info := LocationInfo file_0 42 4 42 26.
  Definition loc_33 : location_info := LocationInfo file_0 42 11 42 25.
  Definition loc_34 : location_info := LocationInfo file_0 43 9 53 3.
  Definition loc_35 : location_info := LocationInfo file_0 44 4 44 48.
  Definition loc_36 : location_info := LocationInfo file_0 45 4 45 21.
  Definition loc_37 : location_info := LocationInfo file_0 46 4 52 5.
  Definition loc_38 : location_info := LocationInfo file_0 46 27 50 5.
  Definition loc_39 : location_info := LocationInfo file_0 47 6 47 22.
  Definition loc_40 : location_info := LocationInfo file_0 48 6 48 24.
  Definition loc_41 : location_info := LocationInfo file_0 49 6 49 18.
  Definition loc_42 : location_info := LocationInfo file_0 49 13 49 17.
  Definition loc_43 : location_info := LocationInfo file_0 49 13 49 17.
  Definition loc_44 : location_info := LocationInfo file_0 48 6 48 16.
  Definition loc_45 : location_info := LocationInfo file_0 48 6 48 10.
  Definition loc_46 : location_info := LocationInfo file_0 48 6 48 10.
  Definition loc_47 : location_info := LocationInfo file_0 48 19 48 23.
  Definition loc_48 : location_info := LocationInfo file_0 48 19 48 23.
  Definition loc_49 : location_info := LocationInfo file_0 47 6 47 8.
  Definition loc_50 : location_info := LocationInfo file_0 47 7 47 8.
  Definition loc_51 : location_info := LocationInfo file_0 47 7 47 8.
  Definition loc_52 : location_info := LocationInfo file_0 47 11 47 21.
  Definition loc_53 : location_info := LocationInfo file_0 47 11 47 21.
  Definition loc_54 : location_info := LocationInfo file_0 47 11 47 15.
  Definition loc_55 : location_info := LocationInfo file_0 47 11 47 15.
  Definition loc_56 : location_info := LocationInfo file_0 47 13 47 14.
  Definition loc_57 : location_info := LocationInfo file_0 47 13 47 14.
  Definition loc_58 : location_info := LocationInfo file_0 50 11 52 5.
  Definition loc_59 : location_info := LocationInfo file_0 51 6 51 18.
  Definition loc_60 : location_info := LocationInfo file_0 51 13 51 17.
  Definition loc_61 : location_info := LocationInfo file_0 51 13 51 17.
  Definition loc_62 : location_info := LocationInfo file_0 46 7 46 25.
  Definition loc_63 : location_info := LocationInfo file_0 46 7 46 12.
  Definition loc_64 : location_info := LocationInfo file_0 46 7 46 12.
  Definition loc_65 : location_info := LocationInfo file_0 46 16 46 25.
  Definition loc_66 : location_info := LocationInfo file_0 46 16 46 25.
  Definition loc_67 : location_info := LocationInfo file_0 46 16 46 20.
  Definition loc_68 : location_info := LocationInfo file_0 46 16 46 20.
  Definition loc_69 : location_info := LocationInfo file_0 46 18 46 19.
  Definition loc_70 : location_info := LocationInfo file_0 46 18 46 19.
  Definition loc_71 : location_info := LocationInfo file_0 45 18 45 20.
  Definition loc_72 : location_info := LocationInfo file_0 45 18 45 20.
  Definition loc_73 : location_info := LocationInfo file_0 45 19 45 20.
  Definition loc_74 : location_info := LocationInfo file_0 45 19 45 20.
  Definition loc_77 : location_info := LocationInfo file_0 44 18 44 47.
  Definition loc_78 : location_info := LocationInfo file_0 44 18 44 27.
  Definition loc_79 : location_info := LocationInfo file_0 44 18 44 27.
  Definition loc_80 : location_info := LocationInfo file_0 44 28 44 39.
  Definition loc_81 : location_info := LocationInfo file_0 44 29 44 39.
  Definition loc_82 : location_info := LocationInfo file_0 44 29 44 33.
  Definition loc_83 : location_info := LocationInfo file_0 44 29 44 33.
  Definition loc_84 : location_info := LocationInfo file_0 44 31 44 32.
  Definition loc_85 : location_info := LocationInfo file_0 44 31 44 32.
  Definition loc_86 : location_info := LocationInfo file_0 44 41 44 46.
  Definition loc_87 : location_info := LocationInfo file_0 44 41 44 46.
  Definition loc_90 : location_info := LocationInfo file_0 41 5 41 25.
  Definition loc_91 : location_info := LocationInfo file_0 41 5 41 7.
  Definition loc_92 : location_info := LocationInfo file_0 41 5 41 7.
  Definition loc_93 : location_info := LocationInfo file_0 41 6 41 7.
  Definition loc_94 : location_info := LocationInfo file_0 41 6 41 7.
  Definition loc_95 : location_info := LocationInfo file_0 41 11 41 25.
  Definition loc_98 : location_info := LocationInfo file_0 63 2 71 3.
  Definition loc_99 : location_info := LocationInfo file_0 63 27 65 3.
  Definition loc_100 : location_info := LocationInfo file_0 64 4 64 11.
  Definition loc_102 : location_info := LocationInfo file_0 65 9 71 3.
  Definition loc_103 : location_info := LocationInfo file_0 66 4 66 26.
  Definition loc_104 : location_info := LocationInfo file_0 67 4 67 40.
  Definition loc_105 : location_info := LocationInfo file_0 68 4 68 23.
  Definition loc_106 : location_info := LocationInfo file_0 69 4 69 17.
  Definition loc_107 : location_info := LocationInfo file_0 70 4 70 22.
  Definition loc_108 : location_info := LocationInfo file_0 70 4 70 10.
  Definition loc_109 : location_info := LocationInfo file_0 70 4 70 10.
  Definition loc_110 : location_info := LocationInfo file_0 70 11 70 12.
  Definition loc_111 : location_info := LocationInfo file_0 70 11 70 12.
  Definition loc_112 : location_info := LocationInfo file_0 70 14 70 20.
  Definition loc_113 : location_info := LocationInfo file_0 70 14 70 20.
  Definition loc_114 : location_info := LocationInfo file_0 69 4 69 13.
  Definition loc_115 : location_info := LocationInfo file_0 69 4 69 13.
  Definition loc_116 : location_info := LocationInfo file_0 69 14 69 15.
  Definition loc_117 : location_info := LocationInfo file_0 69 14 69 15.
  Definition loc_118 : location_info := LocationInfo file_0 68 4 68 13.
  Definition loc_119 : location_info := LocationInfo file_0 68 4 68 13.
  Definition loc_120 : location_info := LocationInfo file_0 68 14 68 21.
  Definition loc_121 : location_info := LocationInfo file_0 68 15 68 21.
  Definition loc_122 : location_info := LocationInfo file_0 67 20 67 39.
  Definition loc_123 : location_info := LocationInfo file_0 67 20 67 29.
  Definition loc_124 : location_info := LocationInfo file_0 67 20 67 29.
  Definition loc_125 : location_info := LocationInfo file_0 67 30 67 31.
  Definition loc_126 : location_info := LocationInfo file_0 67 30 67 31.
  Definition loc_127 : location_info := LocationInfo file_0 67 33 67 38.
  Definition loc_128 : location_info := LocationInfo file_0 67 33 67 38.
  Definition loc_131 : location_info := LocationInfo file_0 66 16 66 25.
  Definition loc_132 : location_info := LocationInfo file_0 66 16 66 25.
  Definition loc_133 : location_info := LocationInfo file_0 66 16 66 20.
  Definition loc_134 : location_info := LocationInfo file_0 66 16 66 20.
  Definition loc_135 : location_info := LocationInfo file_0 66 18 66 19.
  Definition loc_136 : location_info := LocationInfo file_0 66 18 66 19.
  Definition loc_139 : location_info := LocationInfo file_0 63 5 63 25.
  Definition loc_140 : location_info := LocationInfo file_0 63 5 63 7.
  Definition loc_141 : location_info := LocationInfo file_0 63 5 63 7.
  Definition loc_142 : location_info := LocationInfo file_0 63 6 63 7.
  Definition loc_143 : location_info := LocationInfo file_0 63 6 63 7.
  Definition loc_144 : location_info := LocationInfo file_0 63 11 63 25.

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
        if: LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((LocInfoE loc_23 (use{void*} (LocInfoE loc_25 (!{void*} (LocInfoE loc_26 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_27 (NULL)))))
        then
        locinfo: loc_4 ;
          Goto "#1"
        else
        locinfo: loc_11 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_4 ;
        LocInfoE loc_6 (!{void*} (LocInfoE loc_7 ("l"))) <-{ void* }
          LocInfoE loc_8 (use{void*} (LocInfoE loc_9 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        "_" <- LocInfoE loc_13 (global_append) with
          [ LocInfoE loc_14 (&(LocInfoE loc_15 ((LocInfoE loc_16 (!{void*} (LocInfoE loc_18 (!{void*} (LocInfoE loc_19 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_20 (use{void*} (LocInfoE loc_21 ("k"))) ] ;
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
        if: LocInfoE loc_90 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_90 ((LocInfoE loc_91 (use{void*} (LocInfoE loc_93 (!{void*} (LocInfoE loc_94 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_95 (NULL)))))
        then
        locinfo: loc_32 ;
          Goto "#1"
        else
        locinfo: loc_77 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_32 ;
        Return (LocInfoE loc_33 (NULL))
      ]> $
      <[ "#2" :=
        locinfo: loc_77 ;
        "$0" <- LocInfoE loc_79 (global_partition) with
          [ LocInfoE loc_80 (&(LocInfoE loc_81 ((LocInfoE loc_82 (!{void*} (LocInfoE loc_84 (!{void*} (LocInfoE loc_85 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_86 (use{it_layout i32} (LocInfoE loc_87 ("pivot"))) ] ;
        "rest" <-{ void* } LocInfoE loc_77 ("$0") ;
        "head" <-{ void* }
          LocInfoE loc_71 (use{void*} (LocInfoE loc_73 (!{void*} (LocInfoE loc_74 ("l"))))) ;
        locinfo: loc_62 ;
        if: LocInfoE loc_62 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_62 ((LocInfoE loc_63 (use{it_layout i32} (LocInfoE loc_64 ("pivot")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_65 (use{it_layout i32} (LocInfoE loc_66 ((LocInfoE loc_67 (!{void*} (LocInfoE loc_69 (!{void*} (LocInfoE loc_70 ("l")))))) at{struct_list_node} "val")))))))
        then
        locinfo: loc_39 ;
          Goto "#3"
        else
        locinfo: loc_59 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_39 ;
        LocInfoE loc_50 (!{void*} (LocInfoE loc_51 ("l"))) <-{ void* }
          LocInfoE loc_52 (use{void*} (LocInfoE loc_53 ((LocInfoE loc_54 (!{void*} (LocInfoE loc_56 (!{void*} (LocInfoE loc_57 ("l")))))) at{struct_list_node} "next"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_44 ((LocInfoE loc_45 (!{void*} (LocInfoE loc_46 ("head")))) at{struct_list_node} "next") <-{ void* }
          LocInfoE loc_47 (use{void*} (LocInfoE loc_48 ("rest"))) ;
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{void*} (LocInfoE loc_43 ("head"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (use{void*} (LocInfoE loc_61 ("rest"))))
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
        if: LocInfoE loc_139 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_139 ((LocInfoE loc_140 (use{void*} (LocInfoE loc_142 (!{void*} (LocInfoE loc_143 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_144 (NULL)))))
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
        "pivot" <-{ it_layout i32 }
          LocInfoE loc_131 (use{it_layout i32} (LocInfoE loc_132 ((LocInfoE loc_133 (!{void*} (LocInfoE loc_135 (!{void*} (LocInfoE loc_136 ("l")))))) at{struct_list_node} "val"))) ;
        locinfo: loc_122 ;
        "$0" <- LocInfoE loc_124 (global_partition) with
          [ LocInfoE loc_125 (use{void*} (LocInfoE loc_126 ("l"))) ;
          LocInfoE loc_127 (use{it_layout i32} (LocInfoE loc_128 ("pivot"))) ] ;
        "higher" <-{ void* } LocInfoE loc_122 ("$0") ;
        locinfo: loc_105 ;
        "_" <- LocInfoE loc_119 (global_quicksort) with
          [ LocInfoE loc_120 (&(LocInfoE loc_121 ("higher"))) ] ;
        locinfo: loc_106 ;
        "_" <- LocInfoE loc_115 (global_quicksort) with
          [ LocInfoE loc_116 (use{void*} (LocInfoE loc_117 ("l"))) ] ;
        locinfo: loc_107 ;
        "_" <- LocInfoE loc_109 (global_append) with
          [ LocInfoE loc_110 (use{void*} (LocInfoE loc_111 ("l"))) ;
          LocInfoE loc_112 (use{void*} (LocInfoE loc_113 ("higher"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
