From refinedc.typing Require Import typing.

(* pte *)

Record Pte := mk_pte {
  pte_valid : bool;
  pte_type : Z;
  pte_leaf_attr_lo : Z;
  pte_addr : Z;
  pte_undef : Z;
  pte_leaf_attr_hi : Z;
}.

Global Instance Pte_settable : Settable _ := settable! mk_pte
  <pte_valid; pte_type; pte_leaf_attr_lo; pte_addr; pte_undef; pte_leaf_attr_hi>.

Definition empty_pte := {|
  pte_valid := false;
  pte_type := 0;
  pte_leaf_attr_lo := 0;
  pte_addr := 0;
  pte_undef := 0;
  pte_leaf_attr_hi := 0;
|}.

Definition mk_pte_addr (a : addr) : Pte := empty_pte <| pte_addr := a |>.

Definition pte_repr (p : Pte) : Z :=
  bf_cons 0 1 (bool_to_Z $ pte_valid p) $
  bf_cons 1 1 (pte_type p) $
  bf_cons 2 10 (pte_leaf_attr_lo p) $
  bf_cons 12 36 (pte_addr p) $
  bf_cons 48 3 (pte_undef p) $
  bf_cons 51 13 (pte_leaf_attr_hi p) $
  bf_nil.

Arguments pte_repr _/.

Definition pte_wf (p : Pte) : Prop :=
  0 ≤ bool_to_Z $ pte_valid p < 2^1 ∧
  0 ≤ pte_type p < 2^1 ∧
  0 ≤ pte_leaf_attr_lo p < 2^10 ∧
  0 ≤ pte_addr p < 2^36 ∧
  0 ≤ pte_undef p < 2^3 ∧
  0 ≤ pte_leaf_attr_hi p < 2^13.
Global Typeclasses Opaque pte_wf.

Global Instance simpl_pte_wf_impl p :
  SimplImpl (pte_wf p) ltac:(let x := eval unfold pte_wf in (pte_wf p) in exact x).
Proof. done. Qed.

Global Instance Pte_BitfieldDesc : BitfieldDesc Pte := {|
  bitfield_it := u64;
  bitfield_repr := pte_repr;
  bitfield_wf := pte_wf;
|}.

Global Instance simpl_exist_Pte P : SimplExist Pte P
  (∃ valid type leaf_attr_lo addr undef leaf_attr_hi,
    P {|
      pte_valid := valid;
      pte_type := type;
      pte_leaf_attr_lo := leaf_attr_lo;
      pte_addr := addr;
      pte_undef := undef;
      pte_leaf_attr_hi := leaf_attr_hi;
    |}).
Proof. unfold SimplExist. naive_solver. Qed.
Global Instance simpl_forall_Pte P : SimplForall Pte 6 P
  (∀ valid type leaf_attr_lo addr undef leaf_attr_hi,
    P {|
      pte_valid := valid;
      pte_type := type;
      pte_leaf_attr_lo := leaf_attr_lo;
      pte_addr := addr;
      pte_undef := undef;
      pte_leaf_attr_hi := leaf_attr_hi;
    |}).
Proof. unfold SimplForall => ? []. naive_solver. Qed.

Definition addr_of (n : Z) : Z :=
  bf_slice 12 36 n.

(* pte attr *)

Record Attr := {
  attr_lo_s1_attridx : Z;
  attr_lo_s1_ap : Z;
  attr_lo_s1_sh : Z;
  attr_lo_s1_af : bool;
  attr_hi_s1_xn : bool;
}.

Definition attr_repr (a : Attr) : Z :=
  bf_cons 2 2 (attr_lo_s1_attridx a) $
  bf_cons 6 2 (attr_lo_s1_ap a) $
  bf_cons 8 2 (attr_lo_s1_sh a) $
  bf_cons 10 1 (bool_to_Z $ attr_lo_s1_af a) $
  bf_cons 54 1 (bool_to_Z $ attr_hi_s1_xn a)
  bf_nil.

Arguments attr_repr _/.

Definition attr_wf (a : Attr) : Prop :=
  0 ≤ attr_lo_s1_attridx a < 2^2 ∧
  0 ≤ attr_lo_s1_ap a < 2^2 ∧
  0 ≤ attr_lo_s1_sh a < 2^2 ∧
  0 ≤ bool_to_Z $ attr_lo_s1_af a < 2^1 ∧
  0 ≤ bool_to_Z $ attr_hi_s1_xn a < 2^1.
Global Typeclasses Opaque attr_wf.

Global Instance simpl_attr_wf_impl a :
  SimplImpl (attr_wf a) ltac:(let x := eval unfold attr_wf in (attr_wf a) in exact x).
Proof. done. Qed.

Global Instance Attr_BitfieldDesc : BitfieldDesc Attr := {|
  bitfield_it := u64;
  bitfield_repr := attr_repr;
  bitfield_wf := attr_wf;
|}.

(* pte prot *)

Record Prot := {
  prot_x : bool;
  prot_w : bool;
  prot_r : bool;
  prot_device : bool;
}.

Definition prot_repr (p : Prot) : Z :=
  bf_cons 0 1 (bool_to_Z $ prot_x p) $
  bf_cons 1 1 (bool_to_Z $ prot_w p) $
  bf_cons 2 1 (bool_to_Z $ prot_r p) $
  bf_cons 3 1 (bool_to_Z $ prot_device p) $
  bf_nil.

Arguments prot_repr _/.

Definition prot_wf (p : Prot) : Prop :=
  0 ≤ bool_to_Z $ prot_x p < 2^1 ∧
  0 ≤ bool_to_Z $ prot_w p < 2^1 ∧
  0 ≤ bool_to_Z $ prot_r p < 2^1 ∧
  0 ≤ bool_to_Z $ prot_device p < 2^1.
Global Typeclasses Opaque prot_wf.

Global Instance simpl_prot_wf_impl p :
  SimplImpl (prot_wf p) ltac:(let x := eval unfold prot_wf in (prot_wf p) in exact x).
Proof. done. Qed.

Global Instance Prot_BitfieldDesc : BitfieldDesc Prot := {|
  bitfield_it := u64;
  bitfield_repr := prot_repr;
  bitfield_wf := prot_wf;
|}.
Global Instance simpl_exist_Prot P : SimplExist Prot P (∃ x w r device,
  P {| prot_x := x; prot_w := w; prot_r := r; prot_device := device |}).
Proof. unfold SimplExist. naive_solver. Qed.
Global Instance simpl_forall_Prot P : SimplForall Prot 4 P (∀ x w r device,
  P {| prot_x := x; prot_w := w; prot_r := r; prot_device := device |}).
Proof. unfold SimplForall => ? []. naive_solver. Qed.

(* struct, const *)

Record mm_callbacks := {
  virt_to_phys : Z → Z;
}.

Definition max_level : Z := 4.
Definition mtype_device : Z := 5.
Definition mtype_normal : Z := 0.
Definition pte_type_block : Z := 0.
Definition pte_type_page : Z := 1.
Definition pte_type_table : Z := 1.
Definition ap_rw : Z := 1.
Definition ap_ro : Z := 3.
Definition sh_is : Z := 3.
Definition err_code : Z := 22.
