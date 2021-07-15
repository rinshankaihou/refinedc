From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/mpool_simpl.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/mpool_simpl.c".
  Definition loc_2 : location_info := LocationInfo file_0 50 2 50 47.
  Definition loc_3 : location_info := LocationInfo file_0 50 9 50 46.
  Definition loc_4 : location_info := LocationInfo file_0 50 9 50 32.
  Definition loc_5 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_6 : location_info := LocationInfo file_0 50 33 50 37.
  Definition loc_7 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_8 : location_info := LocationInfo file_0 50 39 50 45.
  Definition loc_11 : location_info := LocationInfo file_1 21 4 21 29.
  Definition loc_12 : location_info := LocationInfo file_1 21 4 21 17.
  Definition loc_13 : location_info := LocationInfo file_1 21 4 21 5.
  Definition loc_14 : location_info := LocationInfo file_1 21 4 21 5.
  Definition loc_15 : location_info := LocationInfo file_1 21 20 21 28.
  Definition loc_16 : location_info := LocationInfo file_1 21 27 21 28.
  Definition loc_19 : location_info := LocationInfo file_1 29 4 31 5.
  Definition loc_20 : location_info := LocationInfo file_1 32 4 32 46.
  Definition loc_21 : location_info := LocationInfo file_1 33 4 33 32.
  Definition loc_22 : location_info := LocationInfo file_1 34 4 34 17.
  Definition loc_23 : location_info := LocationInfo file_1 34 11 34 16.
  Definition loc_24 : location_info := LocationInfo file_1 34 11 34 16.
  Definition loc_25 : location_info := LocationInfo file_1 33 4 33 17.
  Definition loc_26 : location_info := LocationInfo file_1 33 4 33 5.
  Definition loc_27 : location_info := LocationInfo file_1 33 4 33 5.
  Definition loc_28 : location_info := LocationInfo file_1 33 20 33 31.
  Definition loc_29 : location_info := LocationInfo file_1 33 20 33 31.
  Definition loc_30 : location_info := LocationInfo file_1 33 20 33 25.
  Definition loc_31 : location_info := LocationInfo file_1 33 20 33 25.
  Definition loc_32 : location_info := LocationInfo file_1 32 32 32 45.
  Definition loc_33 : location_info := LocationInfo file_1 32 32 32 45.
  Definition loc_34 : location_info := LocationInfo file_1 32 32 32 33.
  Definition loc_35 : location_info := LocationInfo file_1 32 32 32 33.
  Definition loc_38 : location_info := LocationInfo file_1 29 35 31 5.
  Definition loc_39 : location_info := LocationInfo file_1 30 8 30 24.
  Definition loc_40 : location_info := LocationInfo file_1 30 15 30 23.
  Definition loc_41 : location_info := LocationInfo file_1 30 22 30 23.
  Definition loc_43 : location_info := LocationInfo file_1 29 8 29 33.
  Definition loc_44 : location_info := LocationInfo file_1 29 8 29 21.
  Definition loc_45 : location_info := LocationInfo file_1 29 8 29 21.
  Definition loc_46 : location_info := LocationInfo file_1 29 8 29 9.
  Definition loc_47 : location_info := LocationInfo file_1 29 8 29 9.
  Definition loc_48 : location_info := LocationInfo file_1 29 25 29 33.
  Definition loc_49 : location_info := LocationInfo file_1 29 32 29 33.
  Definition loc_52 : location_info := LocationInfo file_1 42 4 42 32.
  Definition loc_53 : location_info := LocationInfo file_1 48 4 48 28.
  Definition loc_54 : location_info := LocationInfo file_1 51 4 51 22.
  Definition loc_55 : location_info := LocationInfo file_1 51 4 51 17.
  Definition loc_56 : location_info := LocationInfo file_1 51 4 51 5.
  Definition loc_57 : location_info := LocationInfo file_1 51 4 51 5.
  Definition loc_58 : location_info := LocationInfo file_1 51 20 51 21.
  Definition loc_59 : location_info := LocationInfo file_1 51 20 51 21.
  Definition loc_60 : location_info := LocationInfo file_1 48 4 48 11.
  Definition loc_61 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_62 : location_info := LocationInfo file_1 48 4 48 5.
  Definition loc_63 : location_info := LocationInfo file_1 48 14 48 27.
  Definition loc_64 : location_info := LocationInfo file_1 48 14 48 27.
  Definition loc_65 : location_info := LocationInfo file_1 48 14 48 15.
  Definition loc_66 : location_info := LocationInfo file_1 48 14 48 15.
  Definition loc_67 : location_info := LocationInfo file_1 42 28 42 31.
  Definition loc_68 : location_info := LocationInfo file_1 42 28 42 31.
  Definition loc_73 : location_info := LocationInfo file_1 61 4 61 19.
  Definition loc_74 : location_info := LocationInfo file_1 62 4 62 23.
  Definition loc_75 : location_info := LocationInfo file_1 63 4 63 23.
  Definition loc_76 : location_info := LocationInfo file_1 64 4 64 23.
  Definition loc_77 : location_info := LocationInfo file_1 65 4 65 27.
  Definition loc_78 : location_info := LocationInfo file_1 66 4 66 23.
  Definition loc_79 : location_info := LocationInfo file_1 67 4 67 27.
  Definition loc_80 : location_info := LocationInfo file_1 67 11 67 25.
  Definition loc_81 : location_info := LocationInfo file_1 67 11 67 13.
  Definition loc_82 : location_info := LocationInfo file_1 67 11 67 13.
  Definition loc_83 : location_info := LocationInfo file_1 67 17 67 25.
  Definition loc_84 : location_info := LocationInfo file_1 67 24 67 25.
  Definition loc_85 : location_info := LocationInfo file_1 66 4 66 6.
  Definition loc_86 : location_info := LocationInfo file_1 66 9 66 22.
  Definition loc_87 : location_info := LocationInfo file_1 66 9 66 18.
  Definition loc_88 : location_info := LocationInfo file_1 66 9 66 18.
  Definition loc_89 : location_info := LocationInfo file_1 66 19 66 21.
  Definition loc_90 : location_info := LocationInfo file_1 66 20 66 21.
  Definition loc_91 : location_info := LocationInfo file_1 65 11 65 25.
  Definition loc_92 : location_info := LocationInfo file_1 65 11 65 13.
  Definition loc_93 : location_info := LocationInfo file_1 65 11 65 13.
  Definition loc_94 : location_info := LocationInfo file_1 65 17 65 25.
  Definition loc_95 : location_info := LocationInfo file_1 65 24 65 25.
  Definition loc_96 : location_info := LocationInfo file_1 64 4 64 6.
  Definition loc_97 : location_info := LocationInfo file_1 64 9 64 22.
  Definition loc_98 : location_info := LocationInfo file_1 64 9 64 18.
  Definition loc_99 : location_info := LocationInfo file_1 64 9 64 18.
  Definition loc_100 : location_info := LocationInfo file_1 64 19 64 21.
  Definition loc_101 : location_info := LocationInfo file_1 64 20 64 21.
  Definition loc_102 : location_info := LocationInfo file_1 63 4 63 13.
  Definition loc_103 : location_info := LocationInfo file_1 63 4 63 13.
  Definition loc_104 : location_info := LocationInfo file_1 63 14 63 16.
  Definition loc_105 : location_info := LocationInfo file_1 63 15 63 16.
  Definition loc_106 : location_info := LocationInfo file_1 63 18 63 21.
  Definition loc_107 : location_info := LocationInfo file_1 63 19 63 21.
  Definition loc_108 : location_info := LocationInfo file_1 62 4 62 13.
  Definition loc_109 : location_info := LocationInfo file_1 62 4 62 13.
  Definition loc_110 : location_info := LocationInfo file_1 62 14 62 16.
  Definition loc_111 : location_info := LocationInfo file_1 62 15 62 16.
  Definition loc_112 : location_info := LocationInfo file_1 62 18 62 21.
  Definition loc_113 : location_info := LocationInfo file_1 62 19 62 21.
  Definition loc_114 : location_info := LocationInfo file_1 61 4 61 14.
  Definition loc_115 : location_info := LocationInfo file_1 61 4 61 14.
  Definition loc_116 : location_info := LocationInfo file_1 61 15 61 17.
  Definition loc_117 : location_info := LocationInfo file_1 61 16 61 17.

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
        locinfo: loc_11 ;
        LocInfoE loc_12 ((LocInfoE loc_13 (!{PtrOp} (LocInfoE loc_14 ("p")))) at{struct_mpool} "entry_list") <-{ PtrOp }
          LocInfoE loc_16 (NULL) ;
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
        locinfo: loc_43 ;
        if: LocInfoE loc_43 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_43 ((LocInfoE loc_44 (use{PtrOp} (LocInfoE loc_45 ((LocInfoE loc_46 (!{PtrOp} (LocInfoE loc_47 ("p")))) at{struct_mpool} "entry_list")))) ={PtrOp, PtrOp} (LocInfoE loc_49 (NULL)))))
        then
        locinfo: loc_39 ;
          Goto "#2"
        else
        Goto "#3"
      ]> $
      <[ "#1" :=
        "entry" <-{ PtrOp }
          LocInfoE loc_32 (use{PtrOp} (LocInfoE loc_33 ((LocInfoE loc_34 (!{PtrOp} (LocInfoE loc_35 ("p")))) at{struct_mpool} "entry_list"))) ;
        locinfo: loc_21 ;
        LocInfoE loc_25 ((LocInfoE loc_26 (!{PtrOp} (LocInfoE loc_27 ("p")))) at{struct_mpool} "entry_list") <-{ PtrOp }
          LocInfoE loc_28 (use{PtrOp} (LocInfoE loc_29 ((LocInfoE loc_30 (!{PtrOp} (LocInfoE loc_31 ("entry")))) at{struct_mpool_entry} "next"))) ;
        locinfo: loc_22 ;
        Return (LocInfoE loc_23 (use{PtrOp} (LocInfoE loc_24 ("entry"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_39 ;
        Return (LocInfoE loc_41 (NULL))
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
        "e" <-{ PtrOp }
          LocInfoE loc_67 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_67 (use{PtrOp} (LocInfoE loc_68 ("ptr"))))) ;
        locinfo: loc_53 ;
        LocInfoE loc_60 ((LocInfoE loc_61 (!{PtrOp} (LocInfoE loc_62 ("e")))) at{struct_mpool_entry} "next") <-{ PtrOp }
          LocInfoE loc_63 (use{PtrOp} (LocInfoE loc_64 ((LocInfoE loc_65 (!{PtrOp} (LocInfoE loc_66 ("p")))) at{struct_mpool} "entry_list"))) ;
        locinfo: loc_54 ;
        LocInfoE loc_55 ((LocInfoE loc_56 (!{PtrOp} (LocInfoE loc_57 ("p")))) at{struct_mpool} "entry_list") <-{ PtrOp }
          LocInfoE loc_58 (use{PtrOp} (LocInfoE loc_59 ("e"))) ;
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
        locinfo: loc_73 ;
        expr: (LocInfoE loc_73 (Call (LocInfoE loc_115 (global_mpool_init)) [@{expr} LocInfoE loc_116 (&(LocInfoE loc_117 ("p"))) ])) ;
        locinfo: loc_74 ;
        expr: (LocInfoE loc_74 (Call (LocInfoE loc_109 (global_mpool_put)) [@{expr} LocInfoE loc_110 (&(LocInfoE loc_111 ("p"))) ;
        LocInfoE loc_112 (&(LocInfoE loc_113 (global_e1))) ])) ;
        locinfo: loc_75 ;
        expr: (LocInfoE loc_75 (Call (LocInfoE loc_103 (global_mpool_put)) [@{expr} LocInfoE loc_104 (&(LocInfoE loc_105 ("p"))) ;
        LocInfoE loc_106 (&(LocInfoE loc_107 (global_e2))) ])) ;
        locinfo: loc_76 ;
        LocInfoE loc_96 ("p1") <-{ PtrOp }
          LocInfoE loc_97 (Call (LocInfoE loc_99 (global_mpool_get)) [@{expr} LocInfoE loc_100 (&(LocInfoE loc_101 ("p"))) ]) ;
        locinfo: loc_77 ;
        assert: (LocInfoE loc_91 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_91 ((LocInfoE loc_92 (use{PtrOp} (LocInfoE loc_93 ("p1")))) !={PtrOp, PtrOp} (LocInfoE loc_95 (NULL)))))) ;
        locinfo: loc_78 ;
        LocInfoE loc_85 ("p2") <-{ PtrOp }
          LocInfoE loc_86 (Call (LocInfoE loc_88 (global_mpool_get)) [@{expr} LocInfoE loc_89 (&(LocInfoE loc_90 ("p"))) ]) ;
        locinfo: loc_79 ;
        assert: (LocInfoE loc_80 (UnOp (CastOp $ IntOp bool_it) (IntOp i32) (LocInfoE loc_80 ((LocInfoE loc_81 (use{PtrOp} (LocInfoE loc_82 ("p2")))) !={PtrOp, PtrOp} (LocInfoE loc_84 (NULL)))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
