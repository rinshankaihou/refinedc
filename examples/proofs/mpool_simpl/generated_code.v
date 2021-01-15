From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section code.
  Definition file_0 : string := "examples/mpool_simpl.c".
  Definition loc_2 : location_info := LocationInfo file_0 21 4 21 29.
  Definition loc_3 : location_info := LocationInfo file_0 21 4 21 17.
  Definition loc_4 : location_info := LocationInfo file_0 21 4 21 5.
  Definition loc_5 : location_info := LocationInfo file_0 21 4 21 5.
  Definition loc_6 : location_info := LocationInfo file_0 21 20 21 28.
  Definition loc_7 : location_info := LocationInfo file_0 21 27 21 28.
  Definition loc_10 : location_info := LocationInfo file_0 29 4 31 5.
  Definition loc_11 : location_info := LocationInfo file_0 32 4 32 46.
  Definition loc_12 : location_info := LocationInfo file_0 33 4 33 32.
  Definition loc_13 : location_info := LocationInfo file_0 34 4 34 17.
  Definition loc_14 : location_info := LocationInfo file_0 34 11 34 16.
  Definition loc_15 : location_info := LocationInfo file_0 34 11 34 16.
  Definition loc_16 : location_info := LocationInfo file_0 33 4 33 17.
  Definition loc_17 : location_info := LocationInfo file_0 33 4 33 5.
  Definition loc_18 : location_info := LocationInfo file_0 33 4 33 5.
  Definition loc_19 : location_info := LocationInfo file_0 33 20 33 31.
  Definition loc_20 : location_info := LocationInfo file_0 33 20 33 31.
  Definition loc_21 : location_info := LocationInfo file_0 33 20 33 25.
  Definition loc_22 : location_info := LocationInfo file_0 33 20 33 25.
  Definition loc_23 : location_info := LocationInfo file_0 32 32 32 45.
  Definition loc_24 : location_info := LocationInfo file_0 32 32 32 45.
  Definition loc_25 : location_info := LocationInfo file_0 32 32 32 33.
  Definition loc_26 : location_info := LocationInfo file_0 32 32 32 33.
  Definition loc_29 : location_info := LocationInfo file_0 29 35 31 5.
  Definition loc_30 : location_info := LocationInfo file_0 30 8 30 24.
  Definition loc_31 : location_info := LocationInfo file_0 30 15 30 23.
  Definition loc_32 : location_info := LocationInfo file_0 30 22 30 23.
  Definition loc_34 : location_info := LocationInfo file_0 29 8 29 33.
  Definition loc_35 : location_info := LocationInfo file_0 29 8 29 21.
  Definition loc_36 : location_info := LocationInfo file_0 29 8 29 21.
  Definition loc_37 : location_info := LocationInfo file_0 29 8 29 9.
  Definition loc_38 : location_info := LocationInfo file_0 29 8 29 9.
  Definition loc_39 : location_info := LocationInfo file_0 29 25 29 33.
  Definition loc_40 : location_info := LocationInfo file_0 29 32 29 33.
  Definition loc_43 : location_info := LocationInfo file_0 42 4 42 32.
  Definition loc_44 : location_info := LocationInfo file_0 48 4 48 28.
  Definition loc_45 : location_info := LocationInfo file_0 51 4 51 22.
  Definition loc_46 : location_info := LocationInfo file_0 51 4 51 17.
  Definition loc_47 : location_info := LocationInfo file_0 51 4 51 5.
  Definition loc_48 : location_info := LocationInfo file_0 51 4 51 5.
  Definition loc_49 : location_info := LocationInfo file_0 51 20 51 21.
  Definition loc_50 : location_info := LocationInfo file_0 51 20 51 21.
  Definition loc_51 : location_info := LocationInfo file_0 48 4 48 11.
  Definition loc_52 : location_info := LocationInfo file_0 48 4 48 5.
  Definition loc_53 : location_info := LocationInfo file_0 48 4 48 5.
  Definition loc_54 : location_info := LocationInfo file_0 48 14 48 27.
  Definition loc_55 : location_info := LocationInfo file_0 48 14 48 27.
  Definition loc_56 : location_info := LocationInfo file_0 48 14 48 15.
  Definition loc_57 : location_info := LocationInfo file_0 48 14 48 15.
  Definition loc_58 : location_info := LocationInfo file_0 42 28 42 31.
  Definition loc_59 : location_info := LocationInfo file_0 42 28 42 31.
  Definition loc_64 : location_info := LocationInfo file_0 61 4 61 19.
  Definition loc_65 : location_info := LocationInfo file_0 62 4 62 23.
  Definition loc_66 : location_info := LocationInfo file_0 63 4 63 23.
  Definition loc_67 : location_info := LocationInfo file_0 64 4 64 23.
  Definition loc_68 : location_info := LocationInfo file_0 65 4 65 27.
  Definition loc_69 : location_info := LocationInfo file_0 66 4 66 23.
  Definition loc_70 : location_info := LocationInfo file_0 67 4 67 27.
  Definition loc_71 : location_info := LocationInfo file_0 67 11 67 25.
  Definition loc_72 : location_info := LocationInfo file_0 67 11 67 13.
  Definition loc_73 : location_info := LocationInfo file_0 67 11 67 13.
  Definition loc_74 : location_info := LocationInfo file_0 67 17 67 25.
  Definition loc_75 : location_info := LocationInfo file_0 67 24 67 25.
  Definition loc_76 : location_info := LocationInfo file_0 66 4 66 6.
  Definition loc_77 : location_info := LocationInfo file_0 66 9 66 22.
  Definition loc_78 : location_info := LocationInfo file_0 66 9 66 18.
  Definition loc_79 : location_info := LocationInfo file_0 66 9 66 18.
  Definition loc_80 : location_info := LocationInfo file_0 66 19 66 21.
  Definition loc_81 : location_info := LocationInfo file_0 66 20 66 21.
  Definition loc_82 : location_info := LocationInfo file_0 65 11 65 25.
  Definition loc_83 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_84 : location_info := LocationInfo file_0 65 11 65 13.
  Definition loc_85 : location_info := LocationInfo file_0 65 17 65 25.
  Definition loc_86 : location_info := LocationInfo file_0 65 24 65 25.
  Definition loc_87 : location_info := LocationInfo file_0 64 4 64 6.
  Definition loc_88 : location_info := LocationInfo file_0 64 9 64 22.
  Definition loc_89 : location_info := LocationInfo file_0 64 9 64 18.
  Definition loc_90 : location_info := LocationInfo file_0 64 9 64 18.
  Definition loc_91 : location_info := LocationInfo file_0 64 19 64 21.
  Definition loc_92 : location_info := LocationInfo file_0 64 20 64 21.
  Definition loc_93 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_94 : location_info := LocationInfo file_0 63 4 63 13.
  Definition loc_95 : location_info := LocationInfo file_0 63 14 63 16.
  Definition loc_96 : location_info := LocationInfo file_0 63 15 63 16.
  Definition loc_97 : location_info := LocationInfo file_0 63 18 63 21.
  Definition loc_98 : location_info := LocationInfo file_0 63 19 63 21.
  Definition loc_99 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_100 : location_info := LocationInfo file_0 62 4 62 13.
  Definition loc_101 : location_info := LocationInfo file_0 62 14 62 16.
  Definition loc_102 : location_info := LocationInfo file_0 62 15 62 16.
  Definition loc_103 : location_info := LocationInfo file_0 62 18 62 21.
  Definition loc_104 : location_info := LocationInfo file_0 62 19 62 21.
  Definition loc_105 : location_info := LocationInfo file_0 61 4 61 14.
  Definition loc_106 : location_info := LocationInfo file_0 61 4 61 14.
  Definition loc_107 : location_info := LocationInfo file_0 61 15 61 17.
  Definition loc_108 : location_info := LocationInfo file_0 61 16 61 17.

  (* Definition of struct [mpool_entry]. *)
  Program Definition struct_mpool_entry := {|
    sl_members := [
      (Some "next", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [mpool]. *)
  Program Definition struct_mpool := {|
    sl_members := [
      (Some "entry_list", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [mpool_init]. *)
  Definition impl_mpool_init : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_3 ((LocInfoE loc_4 (!{void*} (LocInfoE loc_5 ("p")))) at{struct_mpool} "entry_list") <-{ void* }
          LocInfoE loc_7 (NULL) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_get]. *)
  Definition impl_mpool_get : function := {|
    f_args := [
      ("p", void*)
    ];
    f_local_vars := [
      ("entry", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_34 ;
        if: LocInfoE loc_34 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_34 ((LocInfoE loc_35 (use{void*} (LocInfoE loc_36 ((LocInfoE loc_37 (!{void*} (LocInfoE loc_38 ("p")))) at{struct_mpool} "entry_list")))) ={PtrOp, PtrOp} (LocInfoE loc_40 (NULL)))))
        then
        locinfo: loc_30 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ void* }
          LocInfoE loc_23 (use{void*} (LocInfoE loc_24 ((LocInfoE loc_25 (!{void*} (LocInfoE loc_26 ("p")))) at{struct_mpool} "entry_list"))) ;
        locinfo: loc_12 ;
        LocInfoE loc_16 ((LocInfoE loc_17 (!{void*} (LocInfoE loc_18 ("p")))) at{struct_mpool} "entry_list") <-{ void* }
          LocInfoE loc_19 (use{void*} (LocInfoE loc_20 ((LocInfoE loc_21 (!{void*} (LocInfoE loc_22 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_13 ;
        Return (LocInfoE loc_14 (use{void*} (LocInfoE loc_15 ("entry"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_30 ;
        Return (LocInfoE loc_32 (NULL))
      ]> $
      <[ "#3" :=
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mpool_put]. *)
  Definition impl_mpool_put : function := {|
    f_args := [
      ("p", void*);
      ("ptr", void*)
    ];
    f_local_vars := [
      ("e", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "e" <-{ void* }
          LocInfoE loc_58 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_58 (use{void*} (LocInfoE loc_59 ("ptr"))))) ;
        locinfo: loc_44 ;
        LocInfoE loc_51 ((LocInfoE loc_52 (!{void*} (LocInfoE loc_53 ("e")))) at{struct_mpool_entry} "next") <-{ void* }
          LocInfoE loc_54 (use{void*} (LocInfoE loc_55 ((LocInfoE loc_56 (!{void*} (LocInfoE loc_57 ("p")))) at{struct_mpool} "entry_list"))) ;
        locinfo: loc_45 ;
        LocInfoE loc_46 ((LocInfoE loc_47 (!{void*} (LocInfoE loc_48 ("p")))) at{struct_mpool} "entry_list") <-{ void* }
          LocInfoE loc_49 (use{void*} (LocInfoE loc_50 ("e"))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (global_e1 global_e2 global_mpool_get global_mpool_init global_mpool_put : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("p1", void*);
      ("p2", void*);
      ("p", layout_of struct_mpool)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_64 ;
        "_" <- LocInfoE loc_106 (global_mpool_init) with
          [ LocInfoE loc_107 (&(LocInfoE loc_108 ("p"))) ] ;
        locinfo: loc_65 ;
        "_" <- LocInfoE loc_100 (global_mpool_put) with
          [ LocInfoE loc_101 (&(LocInfoE loc_102 ("p"))) ;
          LocInfoE loc_103 (&(LocInfoE loc_104 (global_e1))) ] ;
        locinfo: loc_66 ;
        "_" <- LocInfoE loc_94 (global_mpool_put) with
          [ LocInfoE loc_95 (&(LocInfoE loc_96 ("p"))) ;
          LocInfoE loc_97 (&(LocInfoE loc_98 (global_e2))) ] ;
        locinfo: loc_88 ;
        "$1" <- LocInfoE loc_90 (global_mpool_get) with
          [ LocInfoE loc_91 (&(LocInfoE loc_92 ("p"))) ] ;
        locinfo: loc_67 ;
        LocInfoE loc_87 ("p1") <-{ void* } LocInfoE loc_88 ("$1") ;
        locinfo: loc_68 ;
        assert: (LocInfoE loc_82 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_82 ((LocInfoE loc_83 (use{void*} (LocInfoE loc_84 ("p1")))) !={PtrOp, PtrOp} (LocInfoE loc_86 (NULL)))))) ;
        locinfo: loc_77 ;
        "$0" <- LocInfoE loc_79 (global_mpool_get) with
          [ LocInfoE loc_80 (&(LocInfoE loc_81 ("p"))) ] ;
        locinfo: loc_69 ;
        LocInfoE loc_76 ("p2") <-{ void* } LocInfoE loc_77 ("$0") ;
        locinfo: loc_70 ;
        assert: (LocInfoE loc_71 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_71 ((LocInfoE loc_72 (use{void*} (LocInfoE loc_73 ("p2")))) !={PtrOp, PtrOp} (LocInfoE loc_75 (NULL)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
