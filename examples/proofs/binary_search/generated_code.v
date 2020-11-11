From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/binary_search.c]. *)
Section code.
  Definition file_0 : string := "examples/binary_search.c".
  Definition loc_2 : location_info := LocationInfo file_0 22 2 22 19.
  Definition loc_3 : location_info := LocationInfo file_0 28 2 35 3.
  Definition loc_4 : location_info := LocationInfo file_0 36 2 36 11.
  Definition loc_5 : location_info := LocationInfo file_0 36 9 36 10.
  Definition loc_6 : location_info := LocationInfo file_0 36 9 36 10.
  Definition loc_7 : location_info := LocationInfo file_0 28 2 35 3.
  Definition loc_8 : location_info := LocationInfo file_0 28 15 35 3.
  Definition loc_9 : location_info := LocationInfo file_0 29 4 29 28.
  Definition loc_10 : location_info := LocationInfo file_0 30 4 34 5.
  Definition loc_11 : location_info := LocationInfo file_0 28 2 35 3.
  Definition loc_12 : location_info := LocationInfo file_0 28 2 35 3.
  Definition loc_13 : location_info := LocationInfo file_0 30 24 32 7.
  Definition loc_14 : location_info := LocationInfo file_0 31 6 31 16.
  Definition loc_15 : location_info := LocationInfo file_0 31 6 31 7.
  Definition loc_16 : location_info := LocationInfo file_0 31 10 31 15.
  Definition loc_17 : location_info := LocationInfo file_0 31 10 31 11.
  Definition loc_18 : location_info := LocationInfo file_0 31 10 31 11.
  Definition loc_19 : location_info := LocationInfo file_0 31 14 31 15.
  Definition loc_20 : location_info := LocationInfo file_0 32 13 34 5.
  Definition loc_21 : location_info := LocationInfo file_0 33 6 33 12.
  Definition loc_22 : location_info := LocationInfo file_0 33 6 33 7.
  Definition loc_23 : location_info := LocationInfo file_0 33 10 33 11.
  Definition loc_24 : location_info := LocationInfo file_0 33 10 33 11.
  Definition loc_25 : location_info := LocationInfo file_0 30 8 30 22.
  Definition loc_26 : location_info := LocationInfo file_0 30 8 30 12.
  Definition loc_27 : location_info := LocationInfo file_0 30 8 30 12.
  Definition loc_28 : location_info := LocationInfo file_0 30 8 30 12.
  Definition loc_29 : location_info := LocationInfo file_0 30 13 30 18.
  Definition loc_30 : location_info := LocationInfo file_0 30 13 30 18.
  Definition loc_31 : location_info := LocationInfo file_0 30 13 30 18.
  Definition loc_32 : location_info := LocationInfo file_0 30 13 30 15.
  Definition loc_33 : location_info := LocationInfo file_0 30 13 30 15.
  Definition loc_34 : location_info := LocationInfo file_0 30 16 30 17.
  Definition loc_35 : location_info := LocationInfo file_0 30 16 30 17.
  Definition loc_36 : location_info := LocationInfo file_0 30 20 30 21.
  Definition loc_37 : location_info := LocationInfo file_0 30 20 30 21.
  Definition loc_38 : location_info := LocationInfo file_0 29 12 29 27.
  Definition loc_39 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_40 : location_info := LocationInfo file_0 29 12 29 13.
  Definition loc_41 : location_info := LocationInfo file_0 29 16 29 27.
  Definition loc_42 : location_info := LocationInfo file_0 29 16 29 23.
  Definition loc_43 : location_info := LocationInfo file_0 29 17 29 18.
  Definition loc_44 : location_info := LocationInfo file_0 29 17 29 18.
  Definition loc_45 : location_info := LocationInfo file_0 29 21 29 22.
  Definition loc_46 : location_info := LocationInfo file_0 29 21 29 22.
  Definition loc_47 : location_info := LocationInfo file_0 29 26 29 27.
  Definition loc_50 : location_info := LocationInfo file_0 28 8 28 13.
  Definition loc_51 : location_info := LocationInfo file_0 28 8 28 9.
  Definition loc_52 : location_info := LocationInfo file_0 28 8 28 9.
  Definition loc_53 : location_info := LocationInfo file_0 28 12 28 13.
  Definition loc_54 : location_info := LocationInfo file_0 28 12 28 13.
  Definition loc_55 : location_info := LocationInfo file_0 22 17 22 18.
  Definition loc_56 : location_info := LocationInfo file_0 22 17 22 18.
  Definition loc_59 : location_info := LocationInfo file_0 22 10 22 11.

  (* Definition of function [binary_search]. *)
  Definition impl_binary_search : function := {|
    f_args := [
      ("xs", LPtr);
      ("n", it_layout i32);
      ("x", LPtr);
      ("comp", LPtr)
    ];
    f_local_vars := [
      ("r", it_layout i32);
      ("l", it_layout i32);
      ("k", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "l" <-{ it_layout i32 } LocInfoE loc_59 (i2v 0 i32) ;
        "r" <-{ it_layout i32 }
          LocInfoE loc_55 (use{it_layout i32} (LocInfoE loc_56 ("n"))) ;
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_50 ;
        if: LocInfoE loc_50 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_50 ((LocInfoE loc_51 (use{it_layout i32} (LocInfoE loc_52 ("l")))) <{IntOp i32, IntOp i32} (LocInfoE loc_53 (use{it_layout i32} (LocInfoE loc_54 ("r")))))))
        then
        Goto "#2"
        else
        locinfo: loc_4 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "k" <-{ it_layout i32 }
          LocInfoE loc_38 ((LocInfoE loc_39 (use{it_layout i32} (LocInfoE loc_40 ("l")))) +{IntOp i32, IntOp i32} (LocInfoE loc_41 ((LocInfoE loc_42 ((LocInfoE loc_43 (use{it_layout i32} (LocInfoE loc_44 ("r")))) -{IntOp i32, IntOp i32} (LocInfoE loc_45 (use{it_layout i32} (LocInfoE loc_46 ("l")))))) /{IntOp i32, IntOp i32} (LocInfoE loc_47 (i2v 2 i32))))) ;
        locinfo: loc_25 ;
        "$0" <- LocInfoE loc_27 (use{LPtr} (LocInfoE loc_28 ("comp"))) with
          [ LocInfoE loc_29 (use{LPtr} (LocInfoE loc_31 ((LocInfoE loc_32 (!{LPtr} (LocInfoE loc_33 ("xs")))) at_offset{LPtr, PtrOp, IntOp i32} (LocInfoE loc_34 (use{it_layout i32} (LocInfoE loc_35 ("k"))))))) ;
          LocInfoE loc_36 (use{LPtr} (LocInfoE loc_37 ("x"))) ] ;
        locinfo: loc_25 ;
        if: LocInfoE loc_25 ("$0")
        then
        locinfo: loc_14 ;
          Goto "#5"
        else
        locinfo: loc_21 ;
          Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_4 ;
        Return (LocInfoE loc_5 (use{it_layout i32} (LocInfoE loc_6 ("l"))))
      ]> $
      <[ "#4" :=
        locinfo: loc_11 ;
        Goto "continue2"
      ]> $
      <[ "#5" :=
        locinfo: loc_14 ;
        LocInfoE loc_15 ("l") <-{ it_layout i32 }
          LocInfoE loc_16 ((LocInfoE loc_17 (use{it_layout i32} (LocInfoE loc_18 ("k")))) +{IntOp i32, IntOp i32} (LocInfoE loc_19 (i2v 1 i32))) ;
        locinfo: loc_11 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        locinfo: loc_21 ;
        LocInfoE loc_22 ("r") <-{ it_layout i32 }
          LocInfoE loc_23 (use{it_layout i32} (LocInfoE loc_24 ("k"))) ;
        locinfo: loc_11 ;
        Goto "#4"
      ]> $
      <[ "continue2" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
