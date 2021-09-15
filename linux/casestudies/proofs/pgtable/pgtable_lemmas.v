From refinedc.typing Require Import typing.

(* pte *)

Record Pte := {
  pte_valid : bool;
  pte_type : Z;
  pte_leaf_attr_lo : Z;
  pte_addr : Z;
  pte_undef : Z;
  pte_leaf_attr_hi : Z;
}.

Definition pte_set_invalid (pte : Pte) : Pte := {|
  pte_valid := false;
  pte_type := pte_type pte;
  pte_leaf_attr_lo := pte_leaf_attr_lo pte;
  pte_addr := pte_addr pte;
  pte_undef := pte_undef pte;
  pte_leaf_attr_hi := pte_leaf_attr_hi pte;
|}.

Definition mk_pte_addr (a : Z) : Pte := {|
  pte_valid := false;
  pte_type := 0;
  pte_leaf_attr_lo := 0;
  pte_addr := a;
  pte_undef := 0;
  pte_leaf_attr_hi := 0;
|}.

Definition pte_repr (p : Pte) : Z :=
  bf_cons 0 1 (Z_of_bool $ pte_valid p) $
  bf_cons 1 1 (pte_type p) $
  bf_cons 2 10 (pte_leaf_attr_lo p) $
  bf_cons 12 36 (pte_addr p) $
  bf_cons 48 3 (pte_undef p) $
  bf_cons 51 13 (pte_leaf_attr_hi p) $
  bf_nil.

Arguments pte_repr _/.

Definition pte_wf (p : Pte) : Prop :=
  0 ≤ Z_of_bool $ pte_valid p < 2^1 ∧
  0 ≤ pte_type p < 2^1 ∧
  0 ≤ pte_leaf_attr_lo p < 2^10 ∧
  0 ≤ pte_addr p < 2^36 ∧
  0 ≤ pte_undef p < 2^3 ∧
  0 ≤ pte_leaf_attr_hi p < 2^13.

Global Instance Pte_BitfieldDesc : BitfieldDesc Pte := {|
  bitfield_it := u64;
  bitfield_repr := pte_repr;
  bitfield_wf := pte_wf;
|}.

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
  bf_cons 10 1 (Z_of_bool $ attr_lo_s1_af a) $
  bf_cons 54 1 (Z_of_bool $ attr_hi_s1_xn a)
  bf_nil.

Arguments attr_repr _/.

Definition attr_wf (a : Attr) : Prop :=
  0 ≤ attr_lo_s1_attridx a < 2^2 ∧
  0 ≤ attr_lo_s1_ap a < 2^2 ∧
  0 ≤ attr_lo_s1_sh a < 2^2 ∧
  0 ≤ Z_of_bool $ attr_lo_s1_af a < 2^1 ∧
  0 ≤ Z_of_bool $ attr_hi_s1_xn a < 2^1.

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
  bf_cons 0 1 (Z_of_bool $ prot_x p) $
  bf_cons 1 1 (Z_of_bool $ prot_w p) $
  bf_cons 2 1 (Z_of_bool $ prot_r p) $
  bf_cons 3 1 (Z_of_bool $ prot_device p) $
  bf_nil.

Arguments prot_repr _/.

Definition prot_wf (p : Prot) : Prop :=
  0 ≤ Z_of_bool $ prot_x p < 2^1 ∧
  0 ≤ Z_of_bool $ prot_w p < 2^1 ∧
  0 ≤ Z_of_bool $ prot_r p < 2^1 ∧
  0 ≤ Z_of_bool $ prot_device p < 2^1.

Global Instance Prot_BitfieldDesc : BitfieldDesc Prot := {|
  bitfield_it := u64;
  bitfield_repr := prot_repr;
  bitfield_wf := prot_wf;
|}.

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

(* tactics TODO: SimplImpl *)

Ltac simpl_bool_hyp :=
  repeat (match goal with
  | [ H : negb ?b = true  |- _ ] =>
    assert (b = false) by apply negb_true_iff; clear H
  | [ H : negb ?b = false |- _ ] =>
    assert (b = true) by apply negb_false_iff; clear H
  | [ H : bf_cons ?a 1 (Z_of_bool ?b) bf_nil = 0 |- _ ] =>
    assert (b = false) by (by apply (bf_cons_bool_singleton_false_iff a b)); clear H
  | [ H : bf_cons ?a 1 (Z_of_bool ?b) bf_nil ≠ 0 |- _ ] =>
    assert (b = true) by (by apply (bf_cons_bool_singleton_true_iff a b)); clear H
  | [ H : ?b = false |- _ ] => try (rewrite !H; clear H)
  | [ H : ?b = true  |- _ ] => try (rewrite !H; clear H)
  end; try solve_goal).
