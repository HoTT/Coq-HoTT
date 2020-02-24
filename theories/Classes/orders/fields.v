Require Import HoTT.Basics.Decidable.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.interfaces.orders
  HoTT.Classes.theory.rings
  HoTT.Classes.theory.fields.
Require Export
  HoTT.Classes.orders.rings.

Generalizable Variables F f R Fle Flt.

Section contents.
Context `{OrderedField F}.

Lemma pos_recip_compat (x : F) (Px : 0 < x) : 0 < //(x;positive_apart_zero x Px).
Proof.
apply (strictly_order_reflecting (x *.)).
rewrite mult_0_r.
rewrite (recip_inverse' x).
apply lt_0_1.
Qed.

Lemma neg_recip_compat (x : F) (Px : x < 0) : //(x;negative_apart_zero x Px) < 0.
Proof.
  set (negxpos := fst (flip_neg_negate x) Px).
  apply (strictly_order_reflecting ((-x) *.)).
  rewrite mult_0_r.
  rewrite <- negate_mult_distr_l.
  rewrite (recip_inverse' x).
  apply flip_pos_negate, lt_0_1.
Qed.

Lemma flip_lt_recip x y (Py : 0 < y) (ltyx : y < x) :
  let apy0 := positive_apart_zero y Py in
  let apx0 := positive_apart_zero x (transitivity Py ltyx) in
  //(x;apx0) < //(y;apy0).
Proof.
  assert (0 < x) by (transitivity y;trivial).
  apply (strictly_order_reflecting (x *.)).
  rewrite (recip_inverse' x ).
  rewrite mult_comm.
  apply (strictly_order_reflecting (y *.)).
  rewrite mult_assoc, mult_1_r.
  rewrite (recip_inverse' y), mult_1_l; assumption.
Qed.

(* Lemma flip_lt_recip_l' x y (Py : 0 < y) (ltyx : //(y;pseudo_order_lt_apart_flip 0 y Py) < x) : x ≶ 0. *)
(* Proof. *)
(*   apply pseudo_order_lt_apart_flip. *)
(*   refine (transitivity _ ltyx). *)
(*   apply pos_recip_compat. *)
(* Defined. *)
Lemma flip_lt_recip_l x y (Py : 0 < y) (ltyx : //(y;positive_apart_zero y Py) < x) :
  let apx0 := positive_apart_zero x (transitivity (pos_recip_compat y Py) ltyx) in
  //(x;apx0) < y.
Proof.
  set (apy0 := positive_apart_zero y Py).
  set (eq := recip_involutive (y;apy0)).
  set (eq' := ap pr1 eq).
  cbn in eq'.
  rewrite <- eq'.
  unfold recip_on_apart.
  (* need : // (y; apy0) < x *)
  (* have : //(y;pseudo_order_lt_apart_flip 0 y Py) < x *)
  set (ltyx2 := ltyx).
  unfold ltyx2.
  rewrite (recip_irrelevant y (positive_apart_zero y Py) apy0) in ltyx2.
  set (ltyx_recips := flip_lt_recip x (// (y; apy0)) (pos_recip_compat y Py) ltyx2).
  cbn in ltyx_recips.
  rewrite (recip_irrelevant x _ (positive_apart_zero x (transitivity (pos_recip_compat y Py) ltyx))) in ltyx_recips.
  cbn.
  rewrite (recip_irrelevant (//(y;apy0)) _ (recip_apart y apy0)) in ltyx_recips.
  assumption.
Qed.
Lemma flip_lt_recip_r (x y : F) (Px : 0 < x) (Py : 0 < y) (ltyx : y < //(x;positive_apart_zero x Px)) :
  x < //(y;positive_apart_zero y Py).
Proof.
  set (apx0 := positive_apart_zero x Px).
  set (apy0 := positive_apart_zero y Py).
  change x with ((x;apx0) : ApartZero F).1.
  rewrite <- (recip_involutive (x;apx0)).
  unfold recip_on_apart; cbn.
  assert (ltry := pos_recip_compat y Py).
  rewrite (recip_irrelevant y (positive_apart_zero y Py) apy0) in ltry.
  change y with ((y;apy0) : ApartZero F).1 in ltyx.
  rewrite <- (recip_involutive (y;apy0)) in ltyx.
  unfold recip_on_apart in ltyx; cbn in ltyx.
  rewrite (recip_irrelevant (//(y;apy0)) (recip_apart y apy0) (positive_apart_zero (// (y; apy0)) ltry)) in ltyx.
  assert (ltxy := flip_lt_recip_l (// (x; apx0)) (// (y; apy0)) ltry ltyx).
  cbn in ltxy.
  rewrite (recip_irrelevant (//(x;apx0)) (positive_apart_zero (// (x; apx0)) (transitivity (pos_recip_compat (// (y; apy0)) ltry) ltyx)) (recip_apart x apx0)) in ltxy.
  assumption.
Qed.

Lemma field_split2 (x : F) : (x * recip'  2 (positive_apart_zero 2 lt_0_2)) + (x * recip' 2 (positive_apart_zero 2 lt_0_2)) = x.
Proof.
  rewrite <- plus_mult_distr_l.
  rewrite <- (mult_1_l (recip' 2 (positive_apart_zero 2 lt_0_2))).
  rewrite <- plus_mult_distr_r.
  rewrite (recip_inverse' 2 (positive_apart_zero 2 lt_0_2)).
  rewrite mult_1_r.
  reflexivity.
Qed.
End contents.
