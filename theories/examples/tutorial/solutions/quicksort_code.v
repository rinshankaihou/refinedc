From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [theories/examples/tutorial/solutions/quicksort.c]. *)
Section code.
  Definition file_0 : string := "theories/examples/tutorial/solutions/quicksort.c".
  Definition loc_2 : location_info := LocationInfo file_0 24 2 28 3.
  Definition loc_3 : location_info := LocationInfo file_0 24 27 26 3.
  Definition loc_4 : location_info := LocationInfo file_0 25 4 25 11.
  Definition loc_5 : location_info := LocationInfo file_0 25 4 25 6.
  Definition loc_6 : location_info := LocationInfo file_0 25 5 25 6.
  Definition loc_7 : location_info := LocationInfo file_0 25 5 25 6.
  Definition loc_8 : location_info := LocationInfo file_0 25 9 25 10.
  Definition loc_9 : location_info := LocationInfo file_0 25 9 25 10.
  Definition loc_10 : location_info := LocationInfo file_0 26 9 28 3.
  Definition loc_11 : location_info := LocationInfo file_0 27 4 27 27.
  Definition loc_12 : location_info := LocationInfo file_0 27 4 27 10.
  Definition loc_13 : location_info := LocationInfo file_0 27 4 27 10.
  Definition loc_14 : location_info := LocationInfo file_0 27 11 27 22.
  Definition loc_15 : location_info := LocationInfo file_0 27 12 27 22.
  Definition loc_16 : location_info := LocationInfo file_0 27 12 27 16.
  Definition loc_17 : location_info := LocationInfo file_0 27 12 27 16.
  Definition loc_18 : location_info := LocationInfo file_0 27 14 27 15.
  Definition loc_19 : location_info := LocationInfo file_0 27 14 27 15.
  Definition loc_20 : location_info := LocationInfo file_0 27 24 27 25.
  Definition loc_21 : location_info := LocationInfo file_0 27 24 27 25.
  Definition loc_22 : location_info := LocationInfo file_0 24 5 24 25.
  Definition loc_23 : location_info := LocationInfo file_0 24 5 24 7.
  Definition loc_24 : location_info := LocationInfo file_0 24 5 24 7.
  Definition loc_25 : location_info := LocationInfo file_0 24 6 24 7.
  Definition loc_26 : location_info := LocationInfo file_0 24 6 24 7.
  Definition loc_27 : location_info := LocationInfo file_0 24 11 24 25.
  Definition loc_30 : location_info := LocationInfo file_0 39 2 51 3.
  Definition loc_31 : location_info := LocationInfo file_0 39 27 41 3.
  Definition loc_32 : location_info := LocationInfo file_0 40 4 40 26.
  Definition loc_33 : location_info := LocationInfo file_0 40 11 40 25.
  Definition loc_34 : location_info := LocationInfo file_0 41 9 51 3.
  Definition loc_35 : location_info := LocationInfo file_0 42 4 42 48.
  Definition loc_36 : location_info := LocationInfo file_0 43 4 43 21.
  Definition loc_37 : location_info := LocationInfo file_0 44 4 50 5.
  Definition loc_38 : location_info := LocationInfo file_0 44 27 48 5.
  Definition loc_39 : location_info := LocationInfo file_0 45 6 45 22.
  Definition loc_40 : location_info := LocationInfo file_0 46 6 46 24.
  Definition loc_41 : location_info := LocationInfo file_0 47 6 47 18.
  Definition loc_42 : location_info := LocationInfo file_0 47 13 47 17.
  Definition loc_43 : location_info := LocationInfo file_0 47 13 47 17.
  Definition loc_44 : location_info := LocationInfo file_0 46 6 46 16.
  Definition loc_45 : location_info := LocationInfo file_0 46 6 46 10.
  Definition loc_46 : location_info := LocationInfo file_0 46 6 46 10.
  Definition loc_47 : location_info := LocationInfo file_0 46 19 46 23.
  Definition loc_48 : location_info := LocationInfo file_0 46 19 46 23.
  Definition loc_49 : location_info := LocationInfo file_0 45 6 45 8.
  Definition loc_50 : location_info := LocationInfo file_0 45 7 45 8.
  Definition loc_51 : location_info := LocationInfo file_0 45 7 45 8.
  Definition loc_52 : location_info := LocationInfo file_0 45 11 45 21.
  Definition loc_53 : location_info := LocationInfo file_0 45 11 45 21.
  Definition loc_54 : location_info := LocationInfo file_0 45 11 45 15.
  Definition loc_55 : location_info := LocationInfo file_0 45 11 45 15.
  Definition loc_56 : location_info := LocationInfo file_0 45 13 45 14.
  Definition loc_57 : location_info := LocationInfo file_0 45 13 45 14.
  Definition loc_58 : location_info := LocationInfo file_0 48 11 50 5.
  Definition loc_59 : location_info := LocationInfo file_0 49 6 49 18.
  Definition loc_60 : location_info := LocationInfo file_0 49 13 49 17.
  Definition loc_61 : location_info := LocationInfo file_0 49 13 49 17.
  Definition loc_62 : location_info := LocationInfo file_0 44 7 44 25.
  Definition loc_63 : location_info := LocationInfo file_0 44 7 44 16.
  Definition loc_64 : location_info := LocationInfo file_0 44 7 44 16.
  Definition loc_65 : location_info := LocationInfo file_0 44 7 44 11.
  Definition loc_66 : location_info := LocationInfo file_0 44 7 44 11.
  Definition loc_67 : location_info := LocationInfo file_0 44 9 44 10.
  Definition loc_68 : location_info := LocationInfo file_0 44 9 44 10.
  Definition loc_69 : location_info := LocationInfo file_0 44 20 44 25.
  Definition loc_70 : location_info := LocationInfo file_0 44 20 44 25.
  Definition loc_71 : location_info := LocationInfo file_0 43 18 43 20.
  Definition loc_72 : location_info := LocationInfo file_0 43 18 43 20.
  Definition loc_73 : location_info := LocationInfo file_0 43 19 43 20.
  Definition loc_74 : location_info := LocationInfo file_0 43 19 43 20.
  Definition loc_77 : location_info := LocationInfo file_0 42 18 42 47.
  Definition loc_78 : location_info := LocationInfo file_0 42 18 42 27.
  Definition loc_79 : location_info := LocationInfo file_0 42 18 42 27.
  Definition loc_80 : location_info := LocationInfo file_0 42 28 42 39.
  Definition loc_81 : location_info := LocationInfo file_0 42 29 42 39.
  Definition loc_82 : location_info := LocationInfo file_0 42 29 42 33.
  Definition loc_83 : location_info := LocationInfo file_0 42 29 42 33.
  Definition loc_84 : location_info := LocationInfo file_0 42 31 42 32.
  Definition loc_85 : location_info := LocationInfo file_0 42 31 42 32.
  Definition loc_86 : location_info := LocationInfo file_0 42 41 42 46.
  Definition loc_87 : location_info := LocationInfo file_0 42 41 42 46.
  Definition loc_90 : location_info := LocationInfo file_0 39 5 39 25.
  Definition loc_91 : location_info := LocationInfo file_0 39 5 39 7.
  Definition loc_92 : location_info := LocationInfo file_0 39 5 39 7.
  Definition loc_93 : location_info := LocationInfo file_0 39 6 39 7.
  Definition loc_94 : location_info := LocationInfo file_0 39 6 39 7.
  Definition loc_95 : location_info := LocationInfo file_0 39 11 39 25.

  (* Definition of struct [list_node]. *)
  Program Definition struct_list_node := {|
    sl_members := [
      (Some "val", it_layout i32);
      (None, mk_layout 4%nat 0%nat);
      (Some "next", LPtr)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [append]. *)
  Definition impl_append (append : loc): function := {|
    f_args := [
      ("l", LPtr);
      ("k", LPtr)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_22 ;
        if: LocInfoE loc_22 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_22 ((LocInfoE loc_23 (use{LPtr} (LocInfoE loc_25 (!{LPtr} (LocInfoE loc_26 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_27 (NULL)))))
        then
        locinfo: loc_4 ;
          Goto "#1"
        else
        locinfo: loc_11 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_4 ;
        LocInfoE loc_6 (!{LPtr} (LocInfoE loc_7 ("l"))) <-{ LPtr }
          LocInfoE loc_8 (use{LPtr} (LocInfoE loc_9 ("k"))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_11 ;
        "_" <- LocInfoE loc_13 (append) with
          [ LocInfoE loc_14 (&(LocInfoE loc_15 ((LocInfoE loc_16 (!{LPtr} (LocInfoE loc_18 (!{LPtr} (LocInfoE loc_19 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_20 (use{LPtr} (LocInfoE loc_21 ("k"))) ] ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [partition]. *)
  Definition impl_partition (partition : loc): function := {|
    f_args := [
      ("l", LPtr);
      ("pivot", it_layout i32)
    ];
    f_local_vars := [
      ("rest", LPtr);
      ("head", LPtr)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_90 ;
        if: LocInfoE loc_90 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_90 ((LocInfoE loc_91 (use{LPtr} (LocInfoE loc_93 (!{LPtr} (LocInfoE loc_94 ("l")))))) ={PtrOp, PtrOp} (LocInfoE loc_95 (NULL)))))
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
        "$0" <- LocInfoE loc_79 (partition) with
          [ LocInfoE loc_80 (&(LocInfoE loc_81 ((LocInfoE loc_82 (!{LPtr} (LocInfoE loc_84 (!{LPtr} (LocInfoE loc_85 ("l")))))) at{struct_list_node} "next"))) ;
          LocInfoE loc_86 (use{it_layout i32} (LocInfoE loc_87 ("pivot"))) ] ;
        "rest" <-{ LPtr } LocInfoE loc_77 ("$0") ;
        "head" <-{ LPtr }
          LocInfoE loc_71 (use{LPtr} (LocInfoE loc_73 (!{LPtr} (LocInfoE loc_74 ("l"))))) ;
        locinfo: loc_62 ;
        if: LocInfoE loc_62 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_62 ((LocInfoE loc_63 (use{it_layout i32} (LocInfoE loc_64 ((LocInfoE loc_65 (!{LPtr} (LocInfoE loc_67 (!{LPtr} (LocInfoE loc_68 ("l")))))) at{struct_list_node} "val")))) ≤{IntOp i32, IntOp i32} (LocInfoE loc_69 (use{it_layout i32} (LocInfoE loc_70 ("pivot")))))))
        then
        locinfo: loc_39 ;
          Goto "#3"
        else
        locinfo: loc_59 ;
          Goto "#4"
      ]> $
      <[ "#3" :=
        locinfo: loc_39 ;
        LocInfoE loc_50 (!{LPtr} (LocInfoE loc_51 ("l"))) <-{ LPtr }
          LocInfoE loc_52 (use{LPtr} (LocInfoE loc_53 ((LocInfoE loc_54 (!{LPtr} (LocInfoE loc_56 (!{LPtr} (LocInfoE loc_57 ("l")))))) at{struct_list_node} "next"))) ;
        locinfo: loc_40 ;
        LocInfoE loc_44 ((LocInfoE loc_45 (!{LPtr} (LocInfoE loc_46 ("head")))) at{struct_list_node} "next") <-{ LPtr }
          LocInfoE loc_47 (use{LPtr} (LocInfoE loc_48 ("rest"))) ;
        locinfo: loc_41 ;
        Return (LocInfoE loc_42 (use{LPtr} (LocInfoE loc_43 ("head"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_59 ;
        Return (LocInfoE loc_60 (use{LPtr} (LocInfoE loc_61 ("rest"))))
      ]> $∅
    )%E
  |}.
End code.
