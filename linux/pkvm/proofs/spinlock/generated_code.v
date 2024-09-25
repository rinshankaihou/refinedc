From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [linux/pkvm/spinlock.c]. *)
Section code.
  Definition file_0 : string := "linux/pkvm/spinlock.c".
  Definition loc_2 : location_info := LocationInfo file_0 26 2 26 18.
  Definition loc_3 : location_info := LocationInfo file_0 27 2 27 17.
  Definition loc_4 : location_info := LocationInfo file_0 27 2 27 12.
  Definition loc_5 : location_info := LocationInfo file_0 27 2 27 6.
  Definition loc_6 : location_info := LocationInfo file_0 27 2 27 6.
  Definition loc_7 : location_info := LocationInfo file_0 27 2 27 16.
  Definition loc_8 : location_info := LocationInfo file_0 27 15 27 16.
  Definition loc_9 : location_info := LocationInfo file_0 26 2 26 13.
  Definition loc_10 : location_info := LocationInfo file_0 26 2 26 6.
  Definition loc_11 : location_info := LocationInfo file_0 26 2 26 6.
  Definition loc_12 : location_info := LocationInfo file_0 26 2 26 17.
  Definition loc_13 : location_info := LocationInfo file_0 26 16 26 17.
  Definition loc_16 : location_info := LocationInfo file_0 33 2 33 15.
  Definition loc_17 : location_info := LocationInfo file_0 34 2 34 19.
  Definition loc_18 : location_info := LocationInfo file_0 37 2 46 19.
  Definition loc_19 : location_info := LocationInfo file_0 49 2 49 32.
  Definition loc_20 : location_info := LocationInfo file_0 49 30 49 32.
  Definition loc_21 : location_info := LocationInfo file_0 49 8 49 29.
  Definition loc_22 : location_info := LocationInfo file_0 49 8 49 19.
  Definition loc_23 : location_info := LocationInfo file_0 49 8 49 19.
  Definition loc_24 : location_info := LocationInfo file_0 49 8 49 12.
  Definition loc_25 : location_info := LocationInfo file_0 49 8 49 12.
  Definition loc_26 : location_info := LocationInfo file_0 49 23 49 29.
  Definition loc_27 : location_info := LocationInfo file_0 49 23 49 29.
  Definition loc_29 : location_info := LocationInfo file_0 37 5 46 3.
  Definition loc_30 : location_info := LocationInfo file_0 39 4 41 45.
  Definition loc_31 : location_info := LocationInfo file_0 44 4 44 22.
  Definition loc_32 : location_info := LocationInfo file_0 45 4 45 135.
  Definition loc_33 : location_info := LocationInfo file_0 45 4 45 10.
  Definition loc_34 : location_info := LocationInfo file_0 45 13 45 134.
  Definition loc_35 : location_info := LocationInfo file_0 45 13 45 62.
  Definition loc_36 : location_info := LocationInfo file_0 45 63 45 74.
  Definition loc_37 : location_info := LocationInfo file_0 45 64 45 74.
  Definition loc_38 : location_info := LocationInfo file_0 45 64 45 68.
  Definition loc_39 : location_info := LocationInfo file_0 45 64 45 68.
  Definition loc_40 : location_info := LocationInfo file_0 45 76 45 83.
  Definition loc_41 : location_info := LocationInfo file_0 45 76 45 83.
  Definition loc_42 : location_info := LocationInfo file_0 45 77 45 83.
  Definition loc_43 : location_info := LocationInfo file_0 45 85 45 89.
  Definition loc_44 : location_info := LocationInfo file_0 45 85 45 89.
  Definition loc_45 : location_info := LocationInfo file_0 45 85 45 89.
  Definition loc_46 : location_info := LocationInfo file_0 44 4 44 8.
  Definition loc_47 : location_info := LocationInfo file_0 44 11 44 21.
  Definition loc_48 : location_info := LocationInfo file_0 44 11 44 17.
  Definition loc_49 : location_info := LocationInfo file_0 44 11 44 17.
  Definition loc_50 : location_info := LocationInfo file_0 44 20 44 21.
  Definition loc_52 : location_info := LocationInfo file_0 39 7 41 5.
  Definition loc_53 : location_info := LocationInfo file_0 40 6 40 26.
  Definition loc_54 : location_info := LocationInfo file_0 40 6 40 12.
  Definition loc_55 : location_info := LocationInfo file_0 40 15 40 25.
  Definition loc_56 : location_info := LocationInfo file_0 40 15 40 25.
  Definition loc_57 : location_info := LocationInfo file_0 40 15 40 19.
  Definition loc_58 : location_info := LocationInfo file_0 40 15 40 19.
  Definition loc_59 : location_info := LocationInfo file_0 41 12 41 43.
  Definition loc_60 : location_info := LocationInfo file_0 41 12 41 18.
  Definition loc_61 : location_info := LocationInfo file_0 41 12 41 18.
  Definition loc_62 : location_info := LocationInfo file_0 41 22 41 43.
  Definition loc_63 : location_info := LocationInfo file_0 46 10 46 17.
  Definition loc_65 : location_info := LocationInfo file_0 46 11 46 17.
  Definition loc_66 : location_info := LocationInfo file_0 46 11 46 17.
  Definition loc_69 : location_info := LocationInfo file_0 56 2 56 27.
  Definition loc_70 : location_info := LocationInfo file_0 59 2 68 3.
  Definition loc_71 : location_info := LocationInfo file_0 59 43 65 3.
  Definition loc_72 : location_info := LocationInfo file_0 61 4 61 20.
  Definition loc_73 : location_info := LocationInfo file_0 64 4 64 19.
  Definition loc_74 : location_info := LocationInfo file_0 64 4 64 14.
  Definition loc_75 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_76 : location_info := LocationInfo file_0 64 4 64 8.
  Definition loc_77 : location_info := LocationInfo file_0 64 4 64 18.
  Definition loc_78 : location_info := LocationInfo file_0 64 17 64 18.
  Definition loc_79 : location_info := LocationInfo file_0 61 4 61 15.
  Definition loc_80 : location_info := LocationInfo file_0 61 4 61 8.
  Definition loc_81 : location_info := LocationInfo file_0 61 4 61 8.
  Definition loc_82 : location_info := LocationInfo file_0 61 4 61 19.
  Definition loc_83 : location_info := LocationInfo file_0 61 18 61 19.
  Definition loc_84 : location_info := LocationInfo file_0 65 9 68 3.
  Definition loc_85 : location_info := LocationInfo file_0 67 4 67 29.
  Definition loc_86 : location_info := LocationInfo file_0 67 4 67 15.
  Definition loc_87 : location_info := LocationInfo file_0 67 4 67 8.
  Definition loc_88 : location_info := LocationInfo file_0 67 4 67 8.
  Definition loc_89 : location_info := LocationInfo file_0 67 4 67 28.
  Definition loc_90 : location_info := LocationInfo file_0 67 18 67 28.
  Definition loc_91 : location_info := LocationInfo file_0 67 18 67 24.
  Definition loc_92 : location_info := LocationInfo file_0 67 18 67 24.
  Definition loc_93 : location_info := LocationInfo file_0 67 27 67 28.
  Definition loc_94 : location_info := LocationInfo file_0 59 5 59 42.
  Definition loc_95 : location_info := LocationInfo file_0 59 5 59 11.
  Definition loc_96 : location_info := LocationInfo file_0 59 5 59 11.
  Definition loc_97 : location_info := LocationInfo file_0 59 15 59 42.
  Definition loc_98 : location_info := LocationInfo file_0 59 17 59 36.
  Definition loc_99 : location_info := LocationInfo file_0 59 39 59 40.
  Definition loc_100 : location_info := LocationInfo file_0 56 15 56 26.
  Definition loc_101 : location_info := LocationInfo file_0 56 15 56 26.
  Definition loc_102 : location_info := LocationInfo file_0 56 15 56 19.
  Definition loc_103 : location_info := LocationInfo file_0 56 15 56 19.

  (* Definition of struct [__cerbty_unnamed_tag_514]. *)
  Program Definition struct___cerbty_unnamed_tag_514 := {|
    sl_members := [
      (Some "__dummy_max_align_t", void*)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [atomic_flag]. *)
  Program Definition struct_atomic_flag := {|
    sl_members := [
      (Some "_Value", bool_layout)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [hyp_spinlock]. *)
  Program Definition struct_hyp_spinlock := {|
    sl_members := [
      (Some "owner", it_layout u16);
      (Some "next", it_layout u16)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [hyp_spin_lock_init]. *)
  Definition impl_hyp_spin_lock_init : function := {|
    f_args := [
      ("lock", void*)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        LocInfoE loc_9 ((LocInfoE loc_10 (!{PtrOp} (LocInfoE loc_11 ("lock")))) at{struct_hyp_spinlock} "owner") <-{ IntOp u16, ScOrd }
          LocInfoE loc_13 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_13 (i2v 0 i32))) ;
        locinfo: loc_3 ;
        LocInfoE loc_4 ((LocInfoE loc_5 (!{PtrOp} (LocInfoE loc_6 ("lock")))) at{struct_hyp_spinlock} "next") <-{ IntOp u16, ScOrd }
          LocInfoE loc_8 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_8 (i2v 0 i32))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_spin_lock]. *)
  Definition impl_hyp_spin_lock : function := {|
    f_args := [
      ("lock", void*)
    ];
    f_local_vars := [
      ("got_it", bool_layout);
      ("ticket", it_layout u16);
      ("next", it_layout u16)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_18 ;
        Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_63 ;
        if{IntOp i32, None}: LocInfoE loc_63 ((i2v 0 i32) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_65 (UnOp (CastOp $ IntOp i32) (BoolOp) (LocInfoE loc_65 (use{BoolOp} (LocInfoE loc_66 ("got_it")))))))
        then
        locinfo: loc_18 ;
          Goto "#2"
        else
        locinfo: loc_19 ;
          Goto "#3"
      ]> $
      <[ "#2" :=
        locinfo: loc_30 ;
        Goto "#8"
      ]> $
      <[ "#3" :=
        locinfo: loc_19 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_21 ;
        if{IntOp i32, None}: LocInfoE loc_21 ((LocInfoE loc_22 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_22 (use{IntOp u16, ScOrd} (LocInfoE loc_23 ((LocInfoE loc_24 (!{PtrOp} (LocInfoE loc_25 ("lock")))) at{struct_hyp_spinlock} "owner")))))) !={IntOp i32, IntOp i32, i32} (LocInfoE loc_26 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_26 (use{IntOp u16} (LocInfoE loc_27 ("ticket")))))))
        then
        locinfo: loc_19 ;
          Goto "#5"
        else
        Goto "#6"
      ]> $
      <[ "#5" :=
        locinfo: loc_19 ;
        Goto "#4"
      ]> $
      <[ "#6" :=
        Return (VOID)
      ]> $
      <[ "#7" :=
        locinfo: loc_59 ;
        if{IntOp i32, None}: LocInfoE loc_59 ((LocInfoE loc_60 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_60 (use{IntOp u16} (LocInfoE loc_61 ("ticket")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_62 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_62 (i2v (max_int u16) u16)))))
        then
        locinfo: loc_30 ;
          Goto "#8"
        else
        locinfo: loc_31 ;
          Goto "#9"
      ]> $
      <[ "#8" :=
        locinfo: loc_53 ;
        LocInfoE loc_54 ("ticket") <-{ IntOp u16 }
          LocInfoE loc_55 (use{IntOp u16, ScOrd} (LocInfoE loc_56 ((LocInfoE loc_57 (!{PtrOp} (LocInfoE loc_58 ("lock")))) at{struct_hyp_spinlock} "next"))) ;
        Goto "#7"
      ]> $
      <[ "#9" :=
        locinfo: loc_31 ;
        LocInfoE loc_46 ("next") <-{ IntOp u16 }
          LocInfoE loc_47 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_47 ((LocInfoE loc_48 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_48 (use{IntOp u16} (LocInfoE loc_49 ("ticket")))))) +{IntOp i32, IntOp i32} (LocInfoE loc_50 (i2v 1 i32))))) ;
        locinfo: loc_32 ;
        LocInfoE loc_33 ("got_it") <-{ BoolOp } LocInfoE loc_34 (CAS
          (IntOp u16)
          (LocInfoE loc_36 (&(LocInfoE loc_37 ((LocInfoE loc_38 (!{PtrOp} (LocInfoE loc_39 ("lock")))) at{struct_hyp_spinlock} "next"))))
          (LocInfoE loc_40 (UnOp (CastOp $ PtrOp) (PtrOp) (LocInfoE loc_41 (&(LocInfoE loc_42 ("ticket"))))))
          (LocInfoE loc_43 (UnOp (CastOp $ IntOp u16) (IntOp u16) (LocInfoE loc_44 (use{IntOp u16} (LocInfoE loc_45 ("next"))))))) ;
        Goto "#1"
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_spin_unlock]. *)
  Definition impl_hyp_spin_unlock : function := {|
    f_args := [
      ("lock", void*)
    ];
    f_local_vars := [
      ("ticket", it_layout u16)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "ticket" <-{ IntOp u16 }
          LocInfoE loc_100 (use{IntOp u16, ScOrd} (LocInfoE loc_101 ((LocInfoE loc_102 (!{PtrOp} (LocInfoE loc_103 ("lock")))) at{struct_hyp_spinlock} "owner"))) ;
        locinfo: loc_94 ;
        if{IntOp i32, None}: LocInfoE loc_94 ((LocInfoE loc_95 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_95 (use{IntOp u16} (LocInfoE loc_96 ("ticket")))))) ={IntOp i32, IntOp i32, i32} (LocInfoE loc_97 ((LocInfoE loc_98 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_98 (i2v (max_int u16) u16)))) -{IntOp i32, IntOp i32} (LocInfoE loc_99 (i2v 1 i32)))))
        then
        locinfo: loc_72 ;
          Goto "#1"
        else
        locinfo: loc_85 ;
          Goto "#2"
      ]> $
      <[ "#1" :=
        locinfo: loc_72 ;
        LocInfoE loc_79 ((LocInfoE loc_80 (!{PtrOp} (LocInfoE loc_81 ("lock")))) at{struct_hyp_spinlock} "owner") <-{ IntOp u16, ScOrd }
          LocInfoE loc_83 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_83 (i2v 0 i32))) ;
        locinfo: loc_73 ;
        LocInfoE loc_74 ((LocInfoE loc_75 (!{PtrOp} (LocInfoE loc_76 ("lock")))) at{struct_hyp_spinlock} "next") <-{ IntOp u16, ScOrd }
          LocInfoE loc_78 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_78 (i2v 0 i32))) ;
        Return (VOID)
      ]> $
      <[ "#2" :=
        locinfo: loc_85 ;
        LocInfoE loc_86 ((LocInfoE loc_87 (!{PtrOp} (LocInfoE loc_88 ("lock")))) at{struct_hyp_spinlock} "owner") <-{ IntOp u16, ScOrd }
          LocInfoE loc_90 (UnOp (CastOp $ IntOp u16) (IntOp i32) (LocInfoE loc_90 ((LocInfoE loc_91 (UnOp (CastOp $ IntOp i32) (IntOp u16) (LocInfoE loc_91 (use{IntOp u16} (LocInfoE loc_92 ("ticket")))))) +{IntOp i32, IntOp i32} (LocInfoE loc_93 (i2v 1 i32))))) ;
        Return (VOID)
      ]> $∅
    )%E
  |}.
End code.
