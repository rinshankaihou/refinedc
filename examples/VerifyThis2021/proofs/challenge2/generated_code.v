From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [examples/VerifyThis2021/challenge2.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "examples/VerifyThis2021/challenge2.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 29 2 29 38.
  Definition loc_12 : location_info := LocationInfo file_1 30 2 30 34.
  Definition loc_13 : location_info := LocationInfo file_1 30 9 30 33.
  Definition loc_14 : location_info := LocationInfo file_1 30 9 30 29.
  Definition loc_15 : location_info := LocationInfo file_1 30 9 30 17.
  Definition loc_16 : location_info := LocationInfo file_1 30 9 30 17.
  Definition loc_17 : location_info := LocationInfo file_1 30 18 30 28.
  Definition loc_18 : location_info := LocationInfo file_1 30 18 30 28.
  Definition loc_19 : location_info := LocationInfo file_1 30 18 30 22.
  Definition loc_20 : location_info := LocationInfo file_1 30 18 30 22.
  Definition loc_21 : location_info := LocationInfo file_1 30 32 30 33.
  Definition loc_22 : location_info := LocationInfo file_1 29 29 29 38.
  Definition loc_23 : location_info := LocationInfo file_1 29 36 29 37.
  Definition loc_24 : location_info := LocationInfo file_1 29 2 29 38.
  Definition loc_25 : location_info := LocationInfo file_1 29 5 29 27.
  Definition loc_26 : location_info := LocationInfo file_1 29 5 29 9.
  Definition loc_27 : location_info := LocationInfo file_1 29 5 29 9.
  Definition loc_28 : location_info := LocationInfo file_1 29 13 29 27.
  Definition loc_31 : location_info := LocationInfo file_1 39 2 39 17.
  Definition loc_32 : location_info := LocationInfo file_1 45 2 48 3.
  Definition loc_33 : location_info := LocationInfo file_1 50 2 50 13.
  Definition loc_34 : location_info := LocationInfo file_1 50 9 50 12.
  Definition loc_35 : location_info := LocationInfo file_1 50 9 50 12.
  Definition loc_36 : location_info := LocationInfo file_1 45 33 48 3.
  Definition loc_37 : location_info := LocationInfo file_1 46 4 46 22.
  Definition loc_38 : location_info := LocationInfo file_1 47 4 47 13.
  Definition loc_39 : location_info := LocationInfo file_1 47 4 47 7.
  Definition loc_40 : location_info := LocationInfo file_1 47 4 47 12.
  Definition loc_41 : location_info := LocationInfo file_1 47 4 47 7.
  Definition loc_42 : location_info := LocationInfo file_1 47 4 47 7.
  Definition loc_43 : location_info := LocationInfo file_1 47 11 47 12.
  Definition loc_44 : location_info := LocationInfo file_1 46 4 46 8.
  Definition loc_45 : location_info := LocationInfo file_1 46 11 46 21.
  Definition loc_46 : location_info := LocationInfo file_1 46 11 46 21.
  Definition loc_47 : location_info := LocationInfo file_1 46 11 46 15.
  Definition loc_48 : location_info := LocationInfo file_1 46 11 46 15.
  Definition loc_49 : location_info := LocationInfo file_1 45 9 45 31.
  Definition loc_50 : location_info := LocationInfo file_1 45 9 45 13.
  Definition loc_51 : location_info := LocationInfo file_1 45 9 45 13.
  Definition loc_52 : location_info := LocationInfo file_1 45 17 45 31.
  Definition loc_53 : location_info := LocationInfo file_1 39 15 39 16.
  Definition loc_58 : location_info := LocationInfo file_1 64 2 64 23.
  Definition loc_59 : location_info := LocationInfo file_1 66 2 69 3.
  Definition loc_60 : location_info := LocationInfo file_1 71 2 71 44.
  Definition loc_61 : location_info := LocationInfo file_1 72 2 72 20.
  Definition loc_62 : location_info := LocationInfo file_1 74 2 74 56.
  Definition loc_63 : location_info := LocationInfo file_1 75 2 75 20.
  Definition loc_64 : location_info := LocationInfo file_1 77 2 77 14.
  Definition loc_65 : location_info := LocationInfo file_1 77 9 77 13.
  Definition loc_66 : location_info := LocationInfo file_1 77 9 77 13.
  Definition loc_67 : location_info := LocationInfo file_1 75 2 75 12.
  Definition loc_68 : location_info := LocationInfo file_1 75 2 75 6.
  Definition loc_69 : location_info := LocationInfo file_1 75 2 75 6.
  Definition loc_70 : location_info := LocationInfo file_1 75 15 75 19.
  Definition loc_71 : location_info := LocationInfo file_1 75 15 75 19.
  Definition loc_72 : location_info := LocationInfo file_1 74 2 74 6.
  Definition loc_73 : location_info := LocationInfo file_1 74 9 74 55.
  Definition loc_74 : location_info := LocationInfo file_1 74 9 74 23.
  Definition loc_75 : location_info := LocationInfo file_1 74 9 74 23.
  Definition loc_76 : location_info := LocationInfo file_1 74 24 74 34.
  Definition loc_77 : location_info := LocationInfo file_1 74 24 74 34.
  Definition loc_78 : location_info := LocationInfo file_1 74 24 74 28.
  Definition loc_79 : location_info := LocationInfo file_1 74 24 74 28.
  Definition loc_80 : location_info := LocationInfo file_1 74 36 74 41.
  Definition loc_81 : location_info := LocationInfo file_1 74 36 74 41.
  Definition loc_82 : location_info := LocationInfo file_1 74 43 74 54.
  Definition loc_83 : location_info := LocationInfo file_1 74 43 74 50.
  Definition loc_84 : location_info := LocationInfo file_1 74 43 74 44.
  Definition loc_85 : location_info := LocationInfo file_1 74 43 74 44.
  Definition loc_86 : location_info := LocationInfo file_1 74 47 74 50.
  Definition loc_87 : location_info := LocationInfo file_1 74 47 74 48.
  Definition loc_88 : location_info := LocationInfo file_1 74 47 74 48.
  Definition loc_89 : location_info := LocationInfo file_1 74 49 74 50.
  Definition loc_90 : location_info := LocationInfo file_1 74 53 74 54.
  Definition loc_91 : location_info := LocationInfo file_1 72 2 72 12.
  Definition loc_92 : location_info := LocationInfo file_1 72 2 72 6.
  Definition loc_93 : location_info := LocationInfo file_1 72 2 72 6.
  Definition loc_94 : location_info := LocationInfo file_1 72 15 72 19.
  Definition loc_95 : location_info := LocationInfo file_1 72 15 72 19.
  Definition loc_96 : location_info := LocationInfo file_1 71 2 71 6.
  Definition loc_97 : location_info := LocationInfo file_1 71 9 71 43.
  Definition loc_98 : location_info := LocationInfo file_1 71 9 71 23.
  Definition loc_99 : location_info := LocationInfo file_1 71 9 71 23.
  Definition loc_100 : location_info := LocationInfo file_1 71 24 71 28.
  Definition loc_101 : location_info := LocationInfo file_1 71 24 71 28.
  Definition loc_102 : location_info := LocationInfo file_1 71 30 71 35.
  Definition loc_103 : location_info := LocationInfo file_1 71 31 71 35.
  Definition loc_104 : location_info := LocationInfo file_1 71 37 71 42.
  Definition loc_105 : location_info := LocationInfo file_1 71 37 71 38.
  Definition loc_106 : location_info := LocationInfo file_1 71 37 71 38.
  Definition loc_107 : location_info := LocationInfo file_1 71 41 71 42.
  Definition loc_108 : location_info := LocationInfo file_1 66 12 69 3.
  Definition loc_109 : location_info := LocationInfo file_1 67 4 67 18.
  Definition loc_110 : location_info := LocationInfo file_1 68 4 68 26.
  Definition loc_111 : location_info := LocationInfo file_1 68 11 68 25.
  Definition loc_112 : location_info := LocationInfo file_1 67 4 67 10.
  Definition loc_113 : location_info := LocationInfo file_1 67 5 67 10.
  Definition loc_114 : location_info := LocationInfo file_1 67 5 67 10.
  Definition loc_115 : location_info := LocationInfo file_1 67 13 67 17.
  Definition loc_116 : location_info := LocationInfo file_1 67 13 67 17.
  Definition loc_117 : location_info := LocationInfo file_1 66 2 69 3.
  Definition loc_118 : location_info := LocationInfo file_1 66 5 66 11.
  Definition loc_119 : location_info := LocationInfo file_1 66 5 66 6.
  Definition loc_120 : location_info := LocationInfo file_1 66 5 66 6.
  Definition loc_121 : location_info := LocationInfo file_1 66 10 66 11.
  Definition loc_124 : location_info := LocationInfo file_1 88 2 88 29.
  Definition loc_125 : location_info := LocationInfo file_1 89 2 89 12.
  Definition loc_126 : location_info := LocationInfo file_1 90 2 90 41.
  Definition loc_127 : location_info := LocationInfo file_1 90 9 90 40.
  Definition loc_128 : location_info := LocationInfo file_1 90 9 90 23.
  Definition loc_129 : location_info := LocationInfo file_1 90 9 90 23.
  Definition loc_130 : location_info := LocationInfo file_1 90 24 90 28.
  Definition loc_131 : location_info := LocationInfo file_1 90 24 90 28.
  Definition loc_132 : location_info := LocationInfo file_1 90 30 90 36.
  Definition loc_133 : location_info := LocationInfo file_1 90 31 90 36.
  Definition loc_134 : location_info := LocationInfo file_1 90 38 90 39.
  Definition loc_135 : location_info := LocationInfo file_1 90 38 90 39.
  Definition loc_136 : location_info := LocationInfo file_1 88 13 88 28.
  Definition loc_137 : location_info := LocationInfo file_1 88 13 88 22.
  Definition loc_138 : location_info := LocationInfo file_1 88 13 88 22.
  Definition loc_139 : location_info := LocationInfo file_1 88 23 88 27.
  Definition loc_140 : location_info := LocationInfo file_1 88 23 88 27.

  (* Definition of struct [__cerbty_unnamed_tag_486]. *)
  Program Definition struct___cerbty_unnamed_tag_486 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [Node]. *)
  Program Definition struct_Node := {|
    sl_members := [
      (Some "data", it_layout i32);
      (None, Layout 4%nat 0%nat);
      (Some "prev", void*);
      (Some "next", void*)
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

  (* Definition of function [size_rec]. *)
  Definition impl_size_rec (global_size_rec : loc): function := {|
    f_args := [
      ("head", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_25 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_25 ((LocInfoE loc_26 (use{PtrOp} (LocInfoE loc_27 ("head")))) ={PtrOp, PtrOp, i32} (LocInfoE loc_28 (NULL)))
        then
        locinfo: loc_22 ;
          Goto "#2"
        else
        locinfo: loc_12 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_12 ;
        Return (LocInfoE loc_13 ((LocInfoE loc_14 (Call (LocInfoE loc_16 (global_size_rec)) [@{expr} LocInfoE loc_17 (use{PtrOp} (LocInfoE loc_18 ((LocInfoE loc_19 (!{PtrOp} (LocInfoE loc_20 ("head")))) at{struct_Node} "next"))) ])) +{IntOp size_t, IntOp size_t} (LocInfoE loc_21 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_21 (i2v 1 i32))))))
      ]> $
      <[ "#2" :=
        locinfo: loc_22 ;
        Return (LocInfoE loc_23 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_23 (i2v 0 i32))))
      ]> $
      <[ "#3" :=
        locinfo: loc_12 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [size_iter]. *)
  Definition impl_size_iter : function := {|
    f_args := [
      ("head", void*)
    ];
    f_local_vars := [
      ("len", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "len" <-{ IntOp size_t }
          LocInfoE loc_53 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_53 (i2v 0 i32))) ;
        locinfo: loc_32 ;
        Goto "#1"
      ]> $
      <[ "#1" :=
        locinfo: loc_49 ;
        if{IntOp i32, None}: LocInfoE loc_49 ((LocInfoE loc_50 (use{PtrOp} (LocInfoE loc_51 ("head")))) !={PtrOp, PtrOp, i32} (LocInfoE loc_52 (NULL)))
        then
        locinfo: loc_37 ;
          Goto "#2"
        else
        locinfo: loc_33 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_37 ;
        LocInfoE loc_44 ("head") <-{ PtrOp }
          LocInfoE loc_45 (use{PtrOp} (LocInfoE loc_46 ((LocInfoE loc_47 (!{PtrOp} (LocInfoE loc_48 ("head")))) at{struct_Node} "next"))) ;
        locinfo: loc_38 ;
        LocInfoE loc_39 ("len") <-{ IntOp size_t }
          LocInfoE loc_40 ((LocInfoE loc_41 (use{IntOp size_t} (LocInfoE loc_42 ("len")))) +{IntOp size_t, IntOp size_t} (LocInfoE loc_43 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_43 (i2v 1 i32))))) ;
        locinfo: loc_32 ;
        Goto "#1"
      ]> $
      <[ "#3" :=
        locinfo: loc_33 ;
        Return (LocInfoE loc_34 (use{IntOp size_t} (LocInfoE loc_35 ("len"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [dll_to_bst_rec]. *)
  Definition impl_dll_to_bst_rec (global_dll_to_bst_rec : loc): function := {|
    f_args := [
      ("head", void*);
      ("right", void*);
      ("n", it_layout size_t)
    ];
    f_local_vars := [
      ("left", void*);
      ("temp", void*);
      ("root", void*)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_118 ;
        if{IntOp i32, Some "#1"}: LocInfoE loc_118 ((LocInfoE loc_119 (use{IntOp size_t} (LocInfoE loc_120 ("n")))) ={IntOp size_t, IntOp size_t, i32} (LocInfoE loc_121 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_121 (i2v 0 i32)))))
        then
        locinfo: loc_109 ;
          Goto "#2"
        else
        locinfo: loc_60 ;
          Goto "#3"
      ]> $
      <[ "#1" :=
        locinfo: loc_60 ;
        LocInfoE loc_96 ("left") <-{ PtrOp }
          LocInfoE loc_97 (Call (LocInfoE loc_99 (global_dll_to_bst_rec)) [@{expr} LocInfoE loc_100 (use{PtrOp} (LocInfoE loc_101 ("head"))) ;
          LocInfoE loc_102 (&(LocInfoE loc_103 ("root"))) ;
          LocInfoE loc_104 ((LocInfoE loc_105 (use{IntOp size_t} (LocInfoE loc_106 ("n")))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_107 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_107 (i2v 2 i32))))) ]) ;
        locinfo: loc_61 ;
        LocInfoE loc_91 ((LocInfoE loc_92 (!{PtrOp} (LocInfoE loc_93 ("root")))) at{struct_Node} "prev") <-{ PtrOp }
          LocInfoE loc_94 (use{PtrOp} (LocInfoE loc_95 ("left"))) ;
        locinfo: loc_62 ;
        LocInfoE loc_72 ("temp") <-{ PtrOp }
          LocInfoE loc_73 (Call (LocInfoE loc_75 (global_dll_to_bst_rec)) [@{expr} LocInfoE loc_76 (use{PtrOp} (LocInfoE loc_77 ((LocInfoE loc_78 (!{PtrOp} (LocInfoE loc_79 ("root")))) at{struct_Node} "next"))) ;
          LocInfoE loc_80 (use{PtrOp} (LocInfoE loc_81 ("right"))) ;
          LocInfoE loc_82 ((LocInfoE loc_83 ((LocInfoE loc_84 (use{IntOp size_t} (LocInfoE loc_85 ("n")))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_86 ((LocInfoE loc_87 (use{IntOp size_t} (LocInfoE loc_88 ("n")))) /{IntOp size_t, IntOp size_t} (LocInfoE loc_89 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_89 (i2v 2 i32)))))))) -{IntOp size_t, IntOp size_t} (LocInfoE loc_90 (UnOp (CastOp $ IntOp size_t) (IntOp i32) (LocInfoE loc_90 (i2v 1 i32))))) ]) ;
        locinfo: loc_63 ;
        LocInfoE loc_67 ((LocInfoE loc_68 (!{PtrOp} (LocInfoE loc_69 ("root")))) at{struct_Node} "next") <-{ PtrOp }
          LocInfoE loc_70 (use{PtrOp} (LocInfoE loc_71 ("temp"))) ;
        locinfo: loc_64 ;
        Return (LocInfoE loc_65 (use{PtrOp} (LocInfoE loc_66 ("root"))))
      ]> $
      <[ "#2" :=
        locinfo: loc_109 ;
        LocInfoE loc_113 (!{PtrOp} (LocInfoE loc_114 ("right"))) <-{ PtrOp }
          LocInfoE loc_115 (use{PtrOp} (LocInfoE loc_116 ("head"))) ;
        locinfo: loc_110 ;
        Return (LocInfoE loc_111 (NULL))
      ]> $
      <[ "#3" :=
        locinfo: loc_60 ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [dll_to_bst]. *)
  Definition impl_dll_to_bst (global_dll_to_bst_rec global_size_iter : loc): function := {|
    f_args := [
      ("head", void*)
    ];
    f_local_vars := [
      ("right", void*);
      ("n", it_layout size_t)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "n" <-{ IntOp size_t }
          LocInfoE loc_136 (Call (LocInfoE loc_138 (global_size_iter)) [@{expr} LocInfoE loc_139 (use{PtrOp} (LocInfoE loc_140 ("head"))) ]) ;
        locinfo: loc_126 ;
        Return (LocInfoE loc_127 (Call (LocInfoE loc_129 (global_dll_to_bst_rec)) [@{expr} LocInfoE loc_130 (use{PtrOp} (LocInfoE loc_131 ("head"))) ;
               LocInfoE loc_132 (&(LocInfoE loc_133 ("right"))) ;
               LocInfoE loc_134 (use{IntOp size_t} (LocInfoE loc_135 ("n"))) ]))
      ]> $∅
    )%E
  |}.
End code.
