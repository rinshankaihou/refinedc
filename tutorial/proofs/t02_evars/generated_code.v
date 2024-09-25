From caesium Require Export notation.
From caesium Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [tutorial/t02_evars.c]. *)
Section code.
  Definition file_0 : string := "include/refinedc.h".
  Definition file_1 : string := "tutorial/t02_evars.c".
  Definition loc_2 : location_info := LocationInfo file_0 63 2 63 47.
  Definition loc_3 : location_info := LocationInfo file_0 63 9 63 46.
  Definition loc_4 : location_info := LocationInfo file_0 63 9 63 32.
  Definition loc_5 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_6 : location_info := LocationInfo file_0 63 33 63 37.
  Definition loc_7 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_8 : location_info := LocationInfo file_0 63 39 63 45.
  Definition loc_11 : location_info := LocationInfo file_1 26 2 26 9.
  Definition loc_15 : location_info := LocationInfo file_1 64 2 64 9.
  Definition loc_19 : location_info := LocationInfo file_1 80 2 80 11.
  Definition loc_20 : location_info := LocationInfo file_1 80 9 80 10.
  Definition loc_23 : location_info := LocationInfo file_1 114 2 114 9.
  Definition loc_27 : location_info := LocationInfo file_1 154 2 154 12.
  Definition loc_28 : location_info := LocationInfo file_1 154 9 154 11.
  Definition loc_31 : location_info := LocationInfo file_1 197 2 197 12.
  Definition loc_32 : location_info := LocationInfo file_1 197 9 197 11.

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

  (* Definition of function [evar_create]. *)
  Definition impl_evar_create : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_11 ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [evar_create_sidecond]. *)
  Definition impl_evar_create_sidecond : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_15 ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [evar_create_return_int]. *)
  Definition impl_evar_create_return_int : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (i2v 5 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [evar_instantiate_wrong]. *)
  Definition impl_evar_instantiate_wrong : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_23 ;
        Return (VOID)
      ]> $∅
    )%E
  |}.

  (* Definition of function [return_multiple_of_8]. *)
  Definition impl_return_multiple_of_8 : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_27 ;
        Return (LocInfoE loc_28 (i2v 32 i32))
      ]> $∅
    )%E
  |}.

  (* Definition of function [return_multiple_of_5]. *)
  Definition impl_return_multiple_of_5 : function := {|
    f_args := [
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_31 ;
        Return (LocInfoE loc_32 (i2v 20 i32))
      ]> $∅
    )%E
  |}.
End code.
