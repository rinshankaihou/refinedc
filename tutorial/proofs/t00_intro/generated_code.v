From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t00_intro.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t00_intro.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 39 2 39 19.
  Definition loc_12 : location_info := LocationInfo file_1 43 2 52 3.
  Definition loc_13 : location_info := LocationInfo file_1 53 2 53 12.
  Definition loc_14 : location_info := LocationInfo file_1 53 9 53 11.
  Definition loc_15 : location_info := LocationInfo file_1 53 10 53 11.
  Definition loc_16 : location_info := LocationInfo file_1 43 15 52 3.
  Definition loc_17 : location_info := LocationInfo file_1 44 4 44 28.
  Definition loc_18 : location_info := LocationInfo file_1 45 4 51 5.
  Definition loc_19 : location_info := LocationInfo file_1 45 20 47 5.
  Definition loc_20 : location_info := LocationInfo file_1 46 6 46 15.
  Definition loc_21 : location_info := LocationInfo file_1 46 13 46 14.
  Definition loc_22 : location_info := LocationInfo file_1 46 13 46 14.
  Definition loc_23 : location_info := LocationInfo file_1 47 11 51 5.
  Definition loc_24 : location_info := LocationInfo file_1 47 26 49 7.
  Definition loc_25 : location_info := LocationInfo file_1 48 6 48 16.
  Definition loc_26 : location_info := LocationInfo file_1 48 6 48 7.
  Definition loc_27 : location_info := LocationInfo file_1 48 10 48 15.
  Definition loc_28 : location_info := LocationInfo file_1 48 10 48 11.
  Definition loc_29 : location_info := LocationInfo file_1 48 10 48 11.
  Definition loc_30 : location_info := LocationInfo file_1 48 14 48 15.
  Definition loc_31 : location_info := LocationInfo file_1 49 13 51 5.
  Definition loc_32 : location_info := LocationInfo file_1 50 6 50 12.
  Definition loc_33 : location_info := LocationInfo file_1 50 6 50 7.
  Definition loc_34 : location_info := LocationInfo file_1 50 10 50 11.
  Definition loc_35 : location_info := LocationInfo file_1 50 10 50 11.
  Definition loc_36 : location_info := LocationInfo file_1 47 15 47 24.
  Definition loc_37 : location_info := LocationInfo file_1 47 15 47 20.
  Definition loc_38 : location_info := LocationInfo file_1 47 15 47 20.
  Definition loc_39 : location_info := LocationInfo file_1 47 15 47 20.
  Definition loc_40 : location_info := LocationInfo file_1 47 15 47 17.
  Definition loc_41 : location_info := LocationInfo file_1 47 15 47 17.
  Definition loc_42 : location_info := LocationInfo file_1 47 18 47 19.
  Definition loc_43 : location_info := LocationInfo file_1 47 18 47 19.
  Definition loc_44 : location_info := LocationInfo file_1 47 23 47 24.
  Definition loc_45 : location_info := LocationInfo file_1 47 23 47 24.
  Definition loc_46 : location_info := LocationInfo file_1 45 8 45 18.
  Definition loc_47 : location_info := LocationInfo file_1 45 8 45 13.
  Definition loc_48 : location_info := LocationInfo file_1 45 8 45 13.
  Definition loc_49 : location_info := LocationInfo file_1 45 8 45 13.
  Definition loc_50 : location_info := LocationInfo file_1 45 8 45 10.
  Definition loc_51 : location_info := LocationInfo file_1 45 8 45 10.
  Definition loc_52 : location_info := LocationInfo file_1 45 11 45 12.
  Definition loc_53 : location_info := LocationInfo file_1 45 11 45 12.
  Definition loc_54 : location_info := LocationInfo file_1 45 17 45 18.
  Definition loc_55 : location_info := LocationInfo file_1 45 17 45 18.
  Definition loc_56 : location_info := LocationInfo file_1 44 12 44 27.
  Definition loc_57 : location_info := LocationInfo file_1 44 12 44 13.
  Definition loc_58 : location_info := LocationInfo file_1 44 12 44 13.
  Definition loc_59 : location_info := LocationInfo file_1 44 16 44 27.
  Definition loc_60 : location_info := LocationInfo file_1 44 16 44 23.
  Definition loc_61 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_62 : location_info := LocationInfo file_1 44 17 44 18.
  Definition loc_63 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_64 : location_info := LocationInfo file_1 44 21 44 22.
  Definition loc_65 : location_info := LocationInfo file_1 44 26 44 27.
  Definition loc_68 : location_info := LocationInfo file_1 43 8 43 13.
  Definition loc_69 : location_info := LocationInfo file_1 43 8 43 9.
  Definition loc_70 : location_info := LocationInfo file_1 43 8 43 9.
  Definition loc_71 : location_info := LocationInfo file_1 43 12 43 13.
  Definition loc_72 : location_info := LocationInfo file_1 43 12 43 13.
  Definition loc_73 : location_info := LocationInfo file_1 39 17 39 18.
  Definition loc_74 : location_info := LocationInfo file_1 39 17 39 18.
  Definition loc_77 : location_info := LocationInfo file_1 39 10 39 11.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

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

  (* Definition of function [binary_search]. *)
  Definition impl_binary_search : function := {|
    f_args := [
      ("xs", void*);
      ("n", it_layout i32);
      ("x", it_layout i32)
    ];
    f_local_vars := [
      ("r", it_layout i32);
      ("l", it_layout i32);
      ("k", it_layout i32)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "l" <-{ IntOp i32 } LocInfoE loc_77 (i2v 0 i32) ;
        "r" <-{ IntOp i32 }
          LocInfoE loc_73 (use{IntOp i32} (LocInfoE loc_74 ("n"))) ;
        locinfo: loc_12 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_68 ;
        if{IntOp i32, None}: LocInfoE loc_68 ((LocInfoE loc_69 (use{IntOp i32} (LocInfoE loc_70 ("l")))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_71 (use{IntOp i32} (LocInfoE loc_72 ("r")))))
        then
        Goto "#2"
        else
        locinfo: loc_13 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        "k" <-{ IntOp i32 }
          LocInfoE loc_56 ((LocInfoE loc_57 (use{IntOp i32} (LocInfoE loc_58 ("l")))) +{IntOp i32, IntOp i32} (LocInfoE loc_59 ((LocInfoE loc_60 ((LocInfoE loc_61 (use{IntOp i32} (LocInfoE loc_62 ("r")))) -{IntOp i32, IntOp i32} (LocInfoE loc_63 (use{IntOp i32} (LocInfoE loc_64 ("l")))))) /{IntOp i32, IntOp i32} (LocInfoE loc_65 (i2v 2 i32))))) ;
        locinfo: loc_46 ;
        if{IntOp i32, None}: LocInfoE loc_46 ((LocInfoE loc_47 (use{IntOp i32} (LocInfoE loc_49 ((LocInfoE loc_50 (!{PtrOp} (LocInfoE loc_51 ("xs")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_52 (use{IntOp i32} (LocInfoE loc_53 ("k")))))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_54 (use{IntOp i32} (LocInfoE loc_55 ("x")))))
        then
        locinfo: loc_20 ;
          Goto "#4"
        else
        locinfo: loc_36 ;
          Goto "#5"
      ]> $
      <[ "#3" :=
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (UnOp NegOp (IntOp i32) (LocInfoE loc_15 (i2v 1 i32))))
      ]> $
      <[ "#4" :=
        locinfo: loc_20 ;
        Return (LocInfoE loc_21 (use{IntOp i32} (LocInfoE loc_22 ("k"))))
      ]> $
      <[ "#5" :=
        locinfo: loc_36 ;
        if{IntOp i32, None}: LocInfoE loc_36 ((LocInfoE loc_37 (use{IntOp i32} (LocInfoE loc_39 ((LocInfoE loc_40 (!{PtrOp} (LocInfoE loc_41 ("xs")))) at_offset{it_layout i32, PtrOp, IntOp i32} (LocInfoE loc_42 (use{IntOp i32} (LocInfoE loc_43 ("k")))))))) <{IntOp i32, IntOp i32, i32} (LocInfoE loc_44 (use{IntOp i32} (LocInfoE loc_45 ("x")))))
        then
        locinfo: loc_25 ;
          Goto "#6"
        else
        locinfo: loc_32 ;
          Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_25 ;
        LocInfoE loc_26 ("l") <-{ IntOp i32 }
          LocInfoE loc_27 ((LocInfoE loc_28 (use{IntOp i32} (LocInfoE loc_29 ("k")))) +{IntOp i32, IntOp i32} (LocInfoE loc_30 (i2v 1 i32))) ;
        locinfo: loc_12 ;
        Goto "#1"
      ]> $
      <[ "#7" :=
        locinfo: loc_32 ;
        LocInfoE loc_33 ("r") <-{ IntOp i32 }
          LocInfoE loc_34 (use{IntOp i32} (LocInfoE loc_35 ("k"))) ;
        locinfo: loc_12 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.
End code.
