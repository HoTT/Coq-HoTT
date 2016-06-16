(* -*- coding: utf-8 -*- *)
(************************************************************************)
(*  v      *   The Coq Proof Assistant  /  The Coq Development Team     *)
(* <O___,, *   INRIA - CNRS - LIX - LRI - PPS - Copyright 1999-2016     *)
(*   \VV/  **************************************************************)
(*    //   *      This file is distributed under the terms of the       *)
(*         *       GNU Lesser General Public License Version 2.1        *)
(************************************************************************)

Require Import HoTT.Basics.Decidable.
Require Export HoTTClasses.stdlib.BinPosDef.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.theory.additional_operations.

(**********************************************************************)
(** * Binary positive numbers, operations and properties *)
(**********************************************************************)

(** Initial development by Pierre Crégut, CNET, Lannion, France *)

(** The type [positive] and its constructors [xI] and [xO] and [xH]
    are now defined in [BinNums.v] *)

Local Open Scope positive_scope.

Instance: Lt positive := fun x y => (x ?= y) = LT.
Instance: Le positive := fun x y => (x ?= y) = LT \/ (x ?= y) = EQ.

(**********************************************************************)
(** * Properties of operations over positive numbers *)

(** ** Decidability of equality on binary positive numbers *)

Instance xI_inj : Injective xI.
Proof.
split. intros x y E.
apply (ap (fun z => match z with z~1 => z | _ => z end) E).
Defined.

Instance xO_inj : Injective xO.
Proof.
split;intros x y E.
apply (ap (fun z => match z with z~0 => z | _ => z end) E).
Defined.

Lemma xI_xO {x y} : ~ xI x = xO y.
Proof.
intros E.
change ((fun z => match z with z~1 => Unit | _ => Empty end) y~0).
transport E;split.
Qed.

Lemma xO_xI {x y} : ~ xO x = xI y.
Proof.
apply symmetric_neq,xI_xO.
Qed.

Lemma xO_xH {x} : ~ xO x = xH.
Proof.
intros E.
change ((fun z => match z with x~0 => Unit | _ => Empty end) xH).
transport E;split.
Qed.

Lemma xI_xH {x} : ~ xI x = xH.
Proof.
intros E.
change ((fun z => match z with x~1 => Unit | _ => Empty end) xH).
transport E;split.
Qed.

Lemma xH_xI {x} : ~ xH = xI x.
Proof.
apply symmetric_neq,xI_xH.
Qed.

Lemma xH_xO {x} : ~ xH = xO x.
Proof.
apply symmetric_neq,xO_xH.
Qed.

Ltac discr_h H := first [destruct (xI_xO H) | destruct (xO_xI H)
  | destruct (xH_xI H) | destruct (xH_xO H)
  | destruct (xO_xH H) | destruct (xI_xH H)].

Ltac inj_h H := first [apply (injective xO) in H | apply (injective xI) in H].

Ltac destr_eq_h H := (discr_h H || inj_h H); fold add add_carry in H.

Lemma compare_cont_eq : forall r x y, compare_cont r x y = EQ -> r = EQ.
Proof.
intros r x y;revert x y r;induction x as [x Ix|x Ix|];destruct y as [y|y|];
simpl;intros r E;eauto.
- apply Ix in E.
  destruct (GT_EQ E).
- destruct (GT_EQ E).
- apply Ix in E. destruct (LT_EQ E).
- destruct (GT_EQ E).
- destruct (LT_EQ E).
- destruct (LT_EQ E).
Defined.

Lemma compare_eq : forall x y : positive, x ?= y = EQ <-> x = y.
Proof.
induction x as [x Ix|x Ix|];destruct y as [y|y|];
simpl;split;intros E;
first [apply ap, Ix, E | destruct (GT_EQ E) | destruct (LT_EQ E) | idtac].
- apply Ix, (injective xI), E.
- change (compare_cont GT x y = EQ) in E.
  apply compare_cont_eq in E.
  destruct (GT_EQ E).
- destruct (xI_xO E).
- destruct (xI_xH E).
- apply (compare_cont_eq LT) in E. destruct (LT_EQ E).
- destruct (xO_xI E).
- apply Ix, (injective xO), E.
- destruct (xO_xH E).
- destruct (xH_xI E).
- destruct (xH_xO E).
- reflexivity.
- reflexivity.
Defined.

Instance: DecidablePaths positive.
Proof.
hnf.
intros x y.
pose proof (compare_eq x y) as E.
destruct (x ?= y).
- right.
  intros E'. apply LT_EQ,E,E'.
- left. apply E,idpath.
- right.
  intros E'. apply GT_EQ,E,E'.
Defined.

(**********************************************************************)
(** * Properties of successor on binary positive numbers *)

(** ** Specification of [xI] in term of [succ] and [xO] *)

Lemma xI_succ_xO p : p~1 = succ p~0.
Proof.
reflexivity.
Qed.

Lemma succ_discr p : p <> succ p.
Proof.
destruct p;simpl.
- apply xI_xO.
- apply xO_xI.
- apply xH_xO.
Qed.

(** ** Successor and double *)

Lemma pred_double_spec p : pred_double p = pred (p~0).
Proof.
reflexivity.
Qed.

Lemma succ_pred_double p : succ (pred_double p) = p~0.
Proof.
induction p; simpl.
- reflexivity.
- apply ap,IHp.
- reflexivity.
Qed.

Lemma pred_double_succ p : pred_double (succ p) = p~1.
Proof.
induction p; simpl.
- apply ap,IHp.
- reflexivity.
- reflexivity.
Qed.

Lemma double_succ p : (succ p)~0 = succ (succ p~0).
Proof.
destruct p;simpl;trivial.
Qed.

Lemma pred_double_xO_discr p : pred_double p <> p~0.
Proof.
destruct p;simpl.
- apply xI_xO.
- apply xI_xO.
- apply xH_xO.
Qed.

(** ** Successor and predecessor *)

Lemma succ_not_1 p : succ p <> 1.
Proof.
destruct p;simpl;first [apply xO_xH | apply xI_xH].
Qed.

Lemma pred_succ p : pred (succ p) = p.
Proof.
destruct p; simpl; trivial. apply pred_double_succ.
Qed.

Lemma succ_pred_or p : p = 1 \/ succ (pred p) = p.
Proof.
destruct p; simpl; auto.
right; apply succ_pred_double.
Qed.

Lemma succ_pred p : p <> 1 -> succ (pred p) = p.
Proof.
destruct p; intros H; simpl; trivial.
apply succ_pred_double.
destruct H. split.
Qed.

(** ** Injectivity of successor *)

Instance succ_inj : Injective succ.
Proof.
split;intros p q.
revert q.
induction p; intros [q|q| ] H; simpl in H;auto.
- apply ap,IHp,(injective xO),H.
- destruct (xO_xI H).
- apply (injective xO),succ_not_1 in H;destruct H.
- destruct (xI_xO H).
- apply ap,(injective xI),H.
- destruct (xI_xO H).
- apply (injective xO),symmetry,succ_not_1 in H;destruct H.
- destruct (xO_xI H).
Qed.

(** ** Predecessor to [N] *)

Lemma pred_N_succ p : pred_N (succ p) = Npos p.
Proof.
destruct p; simpl; trivial. apply ap, pred_double_succ.
Qed.


(**********************************************************************)
(** * Properties of addition on binary positive numbers *)

(** ** Specification of [succ] in term of [add] *)

Lemma add_1_r p : p + 1 = succ p.
Proof.
destruct p;trivial.
Qed.

Lemma add_1_l p : 1 + p = succ p.
Proof.
destruct p;trivial.
Qed.

(** ** Specification of [add_carry] *)

Theorem add_carry_spec p q : add_carry p q = succ (p + q).
Proof.
revert q. induction p; destruct q; simpl;apply ap;trivial.
Qed.

(** ** Commutativity *)

Instance add_comm : Commutative (plus:Plus positive).
Proof.
intros p. induction p; intros q; destruct q; unfold plus;simpl;auto.
rewrite 2!add_carry_spec. apply ap,ap;auto.
Qed.

(** ** Permutation of [add] and [succ] *)

Theorem add_succ_r p q : p + succ q = succ (p + q).
Proof.
revert q.
induction p; destruct q; unfold plus;simpl; auto using add_1_r;
rewrite add_carry_spec; auto.
Qed.

Theorem add_succ_l p q : succ p + q = succ (p + q).
Proof.
rewrite add_comm, (add_comm p). apply add_succ_r.
Qed.

(** ** No neutral elements for addition *)

Lemma add_no_neutral {p q} : q + p <> p.
Proof.
revert q.
induction p as [p IHp|p IHp| ]; intros [q|q| ] H;unfold plus in H;simpl in H;
destr_eq_h H; eapply IHp;eauto.
Qed.

(** ** Simplification *)

Lemma add_carry_add p q r s :
  add_carry p r = add_carry q s -> p + r = q + s.
Proof.
intros H; apply succ_inj; rewrite <- 2 add_carry_spec;trivial.
Qed.

Instance add_reg_r r : RightCancellation plus r.
Proof.
induction r.
intros [p|p| ] [q|q| ] H; simpl; destr_eq_h H;
rewrite ?add_carry_spec in H;try apply (injective succ) in H.
- apply ap;auto using add_carry_add.
- destruct (add_no_neutral H).
- apply ap;auto.
- apply symmetry,add_no_neutral in H;destruct H.
- split.
- intros [p|p| ] [q|q| ] H; simpl; destr_eq_h H; auto.
  + destruct (add_no_neutral H).
  + destruct (add_no_neutral (symmetry _ _ H)).
- intros p q H. apply succ_inj. rewrite <- 2 add_1_r. trivial.
Qed.

Instance add_reg_l r : LeftCancellation plus r.
Proof.
intros p q. rewrite 2 (add_comm r). apply add_reg_r.
Qed.

Lemma add_cancel_r p q r : p + r = q + r <-> p = q.
Proof.
split. apply add_reg_r. apply (ap (fun z => z + r)).
Qed.

Lemma add_cancel_l p q r : r + p = r + q <-> p = q.
Proof.
split. apply add_reg_l. apply ap.
Qed.

Lemma add_carry_reg_r r : RightCancellation add_carry r.
Proof.
intros p q H. apply add_reg_r with (r:=r); apply add_carry_add;trivial.
Qed.

Lemma add_carry_reg_l r : LeftCancellation add_carry r.
Proof.
intros p q H; apply add_reg_r with (r:=r).
rewrite 2!(add_comm _ r); apply add_carry_add;trivial.
Qed.

(** ** Addition is associative *)

Instance add_assoc : Associative (plus:Plus positive).
Proof.
hnf. intros p. induction p.
- intros [q|q| ] [r|r| ]; simpl; first [apply (ap xI) | apply (ap xO)];
  fold add add_carry; change add with plus; trivial;
  rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
  auto.
- intros [q|q| ] [r|r| ]; simpl; first [apply (ap xI) | apply (ap xO)];
  fold add add_carry; change add with plus; trivial;
  rewrite ?add_carry_spec, ?add_succ_r, ?add_succ_l, ?add_1_r;
  trivial.
  apply ap;auto.
- intros q r; rewrite 2 add_1_l, add_succ_l; auto.
Qed.

(** ** Commutation of addition and double *)

Lemma add_xO p q : (p + q)~0 = p~0 + q~0.
Proof.
destruct p, q;trivial.
Qed.

Lemma add_xI_pred_double p q :
  (p + q)~0 = p~1 + pred_double q.
Proof.
change (p~1) with (p~0 + 1).
rewrite <- add_assoc, add_1_l, succ_pred_double;trivial.
Qed.

Lemma add_xO_pred_double p q :
  pred_double (p + q) = p~0 + pred_double q.
Proof.
revert q. induction p as [p IHp| p IHp| ]; destruct q; simpl;
 rewrite ?add_carry_spec, ?pred_double_succ, ?add_xI_pred_double;
 try reflexivity.
- unfold plus at 2;simpl. change add with plus.
  apply ap. apply symmetry, add_xI_pred_double.
- rewrite IHp; auto.
- rewrite <- succ_pred_double, <- add_1_l. reflexivity.
Qed.

(** ** Miscellaneous *)

Lemma add_diag p : p + p = p~0.
Proof.
induction p as [p IHp| p IHp| ]; unfold plus;simpl;change add with plus;
rewrite ?add_carry_spec, ?IHp;trivial.
Qed.

(**********************************************************************)
(** * Peano induction and recursion on binary positive positive numbers *)

(** The Peano-like recursor function for [positive] (due to Daniel Schepler) *)

Fixpoint peano_rect (P:positive->Type) (a:P 1)
  (f: forall p:positive, P p -> P (succ p)) (p:positive) : P p :=
let f2 := peano_rect (fun p:positive => P (p~0)) (f _ a)
  (fun (p:positive) (x:P (p~0)) => f _ (f _ x))
in
match p with
  | q~1 => f _ (f2 q)
  | q~0 => f2 q
  | 1 => a
end.

Theorem peano_rect_succ (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)) (p:positive) :
  peano_rect P a f (succ p) = f _ (peano_rect P a f p).
Proof.
revert P a f. induction p; trivial.
intros. simpl. rewrite IHp;trivial.
Qed.

Theorem peano_rect_base (P:positive->Type) (a:P 1)
  (f:forall p, P p -> P (succ p)) :
  peano_rect P a f 1 = a.
Proof.
 trivial.
Qed.

Definition peano_rec (P:positive->Set) := peano_rect P.

(** Peano case analysis *)

Theorem peano_case :
  forall P:positive -> Type,
    P 1 -> (forall n:positive, P (succ n)) -> forall p:positive, P p.
Proof.
intros; apply peano_rect; auto.
Qed.


(**********************************************************************)
(** * Properties of multiplication on binary positive numbers *)

(** ** One is neutral for multiplication *)

Local Instance mul_1_l : LeftIdentity mult (1:positive).
Proof.
intro; reflexivity.
Qed.

Local Instance mul_1_r : RightIdentity mult (1:positive).
Proof.
intros p;induction p; simpl; try split.
- apply (ap xI). fold mul. trivial.
- apply (ap xO);fold mul;trivial.
Qed.

(** ** Right reduction properties for multiplication *)

Lemma mul_xO_r p q : p * q~0 = (p * q)~0.
Proof.
induction p; simpl;auto.
- apply (ap xO);fold add mul.
  change mul with mult. rewrite IHp.
  reflexivity.
- apply (ap xO);fold mul;change mul with mult.
  apply IHp.
Qed.

Lemma mul_xI_r p q : p * q~1 = p + (p * q)~0.
Proof.
induction p as [p IHp|p IHp| ]; simpl; first [apply (ap xO)|apply (ap xI)];trivial;
fold add mul;change mul with mult;change add with plus.
rewrite IHp, 2!add_assoc, (add_comm p);trivial.
Qed.

(** ** Commutativity of multiplication *)

Instance mul_comm : Commutative (mult:Mult positive).
Proof.
intros p q;  induction q as [q IHq|q IHq| ];unfold mult;simpl; fold mult;
rewrite <- ? IHq;
auto using mul_xI_r, mul_xO_r, mul_1_r.
Qed.

Lemma mul_xO_l p q : p~0 * q = (p * q)~0.
Proof.
rewrite 2!(mul_comm _ q). apply mul_xO_r.
Qed.

Lemma mul_xI_l p q : p~1 * q = q + (p * q)~0.
Proof.
rewrite (mul_comm _ q) ,mul_xI_r.
rewrite mul_comm;reflexivity.
Qed.

(** ** Distributivity of multiplication over addition *)

Instance mul_add_distr_l : LeftDistribute (mult:Mult positive) plus.
Proof.
hnf. intros p q r.
induction p as [p IHp|p IHp| ];
unfold plus,mult;simpl;fold mult plus;change add with plus.
- rewrite IHp. set (m:=(p*q)~0). set (n:=(p*r)~0).
  change ((p*q+p*r)~0) with (m+n).
  rewrite 2 add_assoc. apply ap2;[|split].
  rewrite <- 2 add_assoc. apply ap,add_comm.
- apply ap; auto.
- reflexivity.
Qed.

Instance mul_add_distr_r : RightDistribute (mult:Mult positive) plus.
Proof.
intros p q r;  rewrite 3 (mul_comm _ r); apply mul_add_distr_l.
Qed.

(** ** Associativity of multiplication *)

Local Instance mul_assoc : Associative (mult:Mult positive).
Proof.
intros p q r;induction p as [p IHp| p IHp | ];
unfold mult; simpl; fold mult; rewrite ?IHp; trivial.
rewrite mul_add_distr_r. reflexivity.
Qed.

Instance mul_monoid : Monoid positive (Aop:=mult) (Aunit:=1).
Proof.
split;[split| |]; apply _.
Qed.

(** ** Successor and multiplication *)

Lemma mul_succ_l p q : (succ p) * q = q + p * q.
Proof.
induction p as [p IHp | p IHp | ]; unfold mult; simpl; fold mult; trivial.
- rewrite IHp, add_assoc, add_diag, <-add_xO. reflexivity.
- symmetry; apply add_diag.
Qed.

Lemma mul_succ_r p q : p * (succ q) = p + p * q.
Proof.
rewrite mul_comm, mul_succ_l. apply ap, mul_comm.
Qed.

(** ** Parity properties of multiplication *)

Lemma mul_xI_mul_xO_discr p q r : p~1 * r <> q~0 * r.
Proof.
induction r.
- intros H. destr_eq_h H.
- intros H;destr_eq_h H. fold mul in H.
  change add with plus in H;change mul with mult in H.
  rewrite 2 mul_xO_r in H.
  auto.
- intros H;destr_eq_h H.
Qed.

Lemma mul_xO_discr p q : p~0 * q <> q.
Proof.
induction q; intros H;destr_eq_h H.
fold mul in H. change mul with mult in H.
rewrite mul_xO_r in H. auto.
Qed.

(** ** Simplification properties of multiplication *)

Instance mul_reg_r r : RightCancellation mult r.
Proof.
intros p q.
revert q r.
induction p as [p IHp| p IHp| ]; intros [q|q| ] r H;try reflexivity.
- unfold mult in H;simpl in H;fold mult in H;change mul with mult in H.
  apply (left_cancellation (+) _),(injective xO) in H.
  apply ap;eauto.
- apply mul_xI_mul_xO_discr in H. destruct H.
- unfold mult in H;simpl in H;fold mult in H;change mul with mult in H.
  rewrite add_comm in H;apply add_no_neutral in H;destruct H.
- symmetry in H. apply mul_xI_mul_xO_discr in H. destruct H.
- unfold mult in H;simpl in H;fold mult in H;change mul with mult in H.
  apply (injective xO) in H. apply ap;eauto.
- apply mul_xO_discr in H. destruct H.
- unfold mult in H;simpl in H;fold mult in H;change mul with mult in H.
  symmetry in H. rewrite add_comm in H;apply add_no_neutral in H.
  destruct H.
- symmetry in H;apply mul_xO_discr in H;destruct H.
Qed.

Instance mul_reg_l r : LeftCancellation mult r.
Proof.
intros p q; rewrite 2 (mul_comm r). apply mul_reg_r.
Qed.

Lemma mul_cancel_r p q r : p * r = q * r <-> p = q.
Proof.
split. apply mul_reg_r. apply (ap (fun z => z * r)).
Qed.

Lemma mul_cancel_l p q r : r * p = r * q <-> p = q.
Proof.
split. apply mul_reg_l. apply ap.
Qed.

(** ** Inversion of multiplication *)

Lemma mul_eq_1_l p q : p * q = 1 -> p = 1.
Proof.
destruct p, q;trivial;intros E;destr_eq_h E.
Qed.

Lemma mul_eq_1_r p q : p * q = 1 -> q = 1.
Proof.
destruct p, q;trivial;intros E;destr_eq_h E.
Qed.

(** ** Square *)

Lemma square_xO p : p~0 * p~0 = (p*p)~0~0.
Proof.
rewrite mul_xO_r,mul_xO_l.
split.
Qed.

Lemma square_xI p : p~1 * p~1 = (p*p+p)~0~1.
Proof.
unfold mult,plus;simpl;fold mult plus;change add with plus.
rewrite mul_comm.
unfold mult,plus;simpl;fold mult plus;change add with plus.
rewrite add_assoc, add_diag.
unfold mult,plus;simpl;fold mult plus;change add with plus.
rewrite add_comm.
reflexivity.
Qed.

(** ** Properties of [iter] *)

Lemma iter_swap_gen : forall A B (f:A->B)(g:A->A)(h:B->B),
 (forall a, f (g a) = h (f a)) -> forall p a,
 f (iter g a p) = iter h (f a) p.
Proof.
induction p; unfold mult,plus;simpl;fold mult plus;change add with plus
; intros; rewrite ?X, ?IHp;auto.
Qed.

Theorem iter_swap :
  forall p (A:Type) (f:A -> A) (x:A),
    iter f (f x) p = f (iter f x p).
Proof.
intros. symmetry. apply iter_swap_gen. split.
Qed.

Theorem iter_succ :
  forall p (A:Type) (f:A -> A) (x:A),
    iter f x (succ p) = f (iter f x p).
Proof.
induction p as [p IHp|p IHp|]; intros; simpl; trivial.
rewrite !IHp, iter_swap. trivial.
Qed.

Theorem iter_add :
  forall p q (A:Type) (f:A -> A) (x:A),
    iter f x (p+q) = iter f (iter f x q) p.
Proof.
induction p using peano_rect; intros.
- rewrite add_1_l, iter_succ;trivial.
- rewrite add_succ_l, !iter_succ, IHp;trivial.
Qed.

Theorem iter_invariant :
  forall (p:positive) (A:Type) (f:A -> A) (Inv:A -> Type),
    (forall x:A, Inv x -> Inv (f x)) ->
    forall x:A, Inv x -> Inv (iter f x p).
Proof.
induction p as [p IHp|p IHp|]; simpl; trivial.
- intros A f Inv H x H0. apply H, IHp, IHp; trivial.
- intros A f Inv H x H0. apply IHp, IHp; trivial.
Qed.

(** ** Properties of power *)

Lemma pow_1_r p : p ** 1 = p.
Proof.
unfold pow,Ppow. simpl. apply right_identity.
Qed.

Lemma pow_succ_r p q : p ** (succ q) = p * p ** q.
Proof.
unfold pow,Ppow. rewrite iter_succ.
reflexivity.
Qed.

(** ** Properties of square *)

Lemma square_spec p : square p = p * p.
Proof.
induction p.
- rewrite square_xI. simpl. rewrite IHp. trivial.
- rewrite square_xO. simpl. rewrite IHp. trivial.
- trivial.
Qed.

(** ** Properties of [sub_mask] *)
(* 
Lemma sub_mask_succ_r p q :
  sub_mask p (succ q) = sub_mask_carry p q.
Proof.
 revert q. induction p; destruct q; simpl; f_equal; trivial; now destruct p.
Qed.

Theorem sub_mask_carry_spec p q :
  sub_mask_carry p q = pred_mask (sub_mask p q).
Proof.
  revert q. induction p as [p IHp|p IHp| ]; destruct q; simpl;
   try reflexivity; rewrite ?IHp;
   destruct (sub_mask p q) as [|[r|r| ]|] || destruct p; auto.
Qed.

Inductive SubMaskSpec (p q : positive) : mask -> Prop :=
 | SubIsNul : p = q -> SubMaskSpec p q IsNul
 | SubIsPos : forall r, q + r = p -> SubMaskSpec p q (IsPos r)
 | SubIsNeg : forall r, p + r = q -> SubMaskSpec p q IsNeg.

Theorem sub_mask_spec p q : SubMaskSpec p q (sub_mask p q).
Proof.
 revert q. induction p; destruct q; simpl; try constructor; trivial.
 (* p~1 q~1 *)
 destruct (IHp q); subst; try now constructor.
  now apply SubIsNeg with r~0.
 (* p~1 q~0 *)
 destruct (IHp q); subst; try now constructor.
  apply SubIsNeg with (pred_double r). symmetry. apply add_xI_pred_double.
 (* p~0 q~1 *)
 rewrite sub_mask_carry_spec.
 destruct (IHp q); subst; try constructor.
  now apply SubIsNeg with 1.
  destruct r; simpl; try constructor; simpl.
   now rewrite add_carry_spec, <- add_succ_r.
   now rewrite add_carry_spec, <- add_succ_r, succ_pred_double.
   now rewrite add_1_r.
  now apply SubIsNeg with r~1.
 (* p~0 q~0 *)
 destruct (IHp q); subst; try now constructor.
  now apply SubIsNeg with r~0.
 (* p~0 1 *)
 now rewrite add_1_l, succ_pred_double.
 (* 1 q~1 *)
 now apply SubIsNeg with q~0.
 (* 1 q~0 *)
 apply SubIsNeg with (pred_double q). now rewrite add_1_l, succ_pred_double.
Qed.

Theorem sub_mask_nul_iff p q : sub_mask p q = IsNul <-> p = q.
Proof.
 split.
 now case sub_mask_spec.
 intros <-. induction p; simpl; now rewrite ?IHp.
Qed.

Theorem sub_mask_diag p : sub_mask p p = IsNul.
Proof.
  now apply sub_mask_nul_iff.
Qed.

Lemma sub_mask_add p q r : sub_mask p q = IsPos r -> q + r = p.
Proof.
 case sub_mask_spec; congruence.
Qed.

Lemma sub_mask_add_diag_l p q : sub_mask (p+q) p = IsPos q.
Proof.
 case sub_mask_spec.
 intros H. rewrite add_comm in H. elim (add_no_neutral _ _ H).
 intros r H. apply add_cancel_l in H. now f_equal.
 intros r H. rewrite <- add_assoc, add_comm in H. elim (add_no_neutral _ _ H).
Qed.

Lemma sub_mask_pos_iff p q r : sub_mask p q = IsPos r <-> q + r = p.
Proof.
 split. apply sub_mask_add. intros <-; apply sub_mask_add_diag_l.
Qed.

Lemma sub_mask_add_diag_r p q : sub_mask p (p+q) = IsNeg.
Proof.
 case sub_mask_spec; trivial.
 intros H. symmetry in H; rewrite add_comm in H. elim (add_no_neutral _ _ H).
 intros r H. rewrite <- add_assoc, add_comm in H. elim (add_no_neutral _ _ H).
Qed.

Lemma sub_mask_neg_iff p q : sub_mask p q = IsNeg <-> exists r, p + r = q.
Proof.
 split.
 case sub_mask_spec; try discriminate. intros r Hr _; now exists r.
 intros (r,<-). apply sub_mask_add_diag_r.
Qed.

(*********************************************************************)
(** * Properties of boolean comparisons *)

Theorem eqb_eq p q : (p =? q) = true <-> p=q.
Proof.
 revert q. induction p; destruct q; simpl; rewrite ?IHp; split; congruence.
Qed.

Theorem ltb_lt p q : (p <? q) = true <-> p < q.
Proof.
  unfold ltb, lt. destruct compare; easy'.
Qed.

Theorem leb_le p q : (p <=? q) = true <-> p <= q.
Proof.
  unfold leb, le. destruct compare; easy'.
Qed.

(** More about [eqb] *)

Include BoolEqualityFacts.

(**********************************************************************)
(** * Properties of comparison on binary positive numbers *)

(** First, we express [compare_cont] in term of [compare] *)

Definition switch_Eq c c' :=
 match c' with
  | Eq => c
  | Lt => Lt
  | Gt => Gt
 end.

Lemma compare_cont_spec p q c :
  compare_cont c p q = switch_Eq c (p ?= q).
Proof.
  unfold compare.
  revert q c.
  induction p; destruct q; simpl; trivial.
  intros c.
  rewrite 2 IHp. now destruct (compare_cont Eq p q).
  intros c.
  rewrite 2 IHp. now destruct (compare_cont Eq p q).
Qed.

(** From this general result, we now describe particular cases
    of [compare_cont p q c = c'] :
    - When [c=Eq], this is directly [compare]
    - When [c<>Eq], we'll show first that [c'<>Eq]
    - That leaves only 4 lemmas for [c] and [c'] being [Lt] or [Gt]
*)

Theorem compare_cont_Eq p q c :
 compare_cont c p q = Eq -> c = Eq.
Proof.
  rewrite compare_cont_spec. now destruct (p ?= q).
Qed.

Lemma compare_cont_Lt_Gt p q :
  compare_cont Lt p q = Gt <-> p > q.
Proof.
  rewrite compare_cont_spec. unfold gt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Lt_Lt p q :
  compare_cont Lt p q = Lt <-> p <= q.
Proof.
  rewrite compare_cont_spec. unfold le. destruct (p ?= q); easy'.
Qed.

Lemma compare_cont_Gt_Lt p q :
  compare_cont Gt p q = Lt <-> p < q.
Proof.
  rewrite compare_cont_spec. unfold lt. destruct (p ?= q); now split.
Qed.

Lemma compare_cont_Gt_Gt p q :
  compare_cont Gt p q = Gt <-> p >= q.
Proof.
  rewrite compare_cont_spec. unfold ge. destruct (p ?= q); easy'.
Qed.

(** We can express recursive equations for [compare] *)

Lemma compare_xO_xO p q : (p~0 ?= q~0) = (p ?= q).
Proof. reflexivity. Qed.

Lemma compare_xI_xI p q : (p~1 ?= q~1) = (p ?= q).
Proof. reflexivity. Qed.

Lemma compare_xI_xO p q :
 (p~1 ?= q~0) = switch_Eq Gt (p ?= q).
Proof. exact (compare_cont_spec p q Gt). Qed.

Lemma compare_xO_xI p q :
 (p~0 ?= q~1) = switch_Eq Lt (p ?= q).
Proof. exact (compare_cont_spec p q Lt). Qed.

Hint Rewrite compare_xO_xO compare_xI_xI compare_xI_xO compare_xO_xI : compare.

Ltac simpl_compare := autorewrite with compare.
Ltac simpl_compare_in H := autorewrite with compare in H.

(** Relation between [compare] and [sub_mask] *)

Definition mask2cmp (p:mask) : comparison :=
 match p with
  | IsNul => Eq
  | IsPos _ => Gt
  | IsNeg => Lt
 end.

Lemma compare_sub_mask p q : (p ?= q) = mask2cmp (sub_mask p q).
Proof.
  revert q.
  induction p as [p IHp| p IHp| ]; intros [q|q| ]; simpl; trivial;
  specialize (IHp q); rewrite ?sub_mask_carry_spec;
  destruct (sub_mask p q) as [|r|]; simpl in *;
  try clear r; try destruct r; simpl; trivial;
  simpl_compare; now rewrite IHp.
Qed.

(** Alternative characterisation of strict order in term of addition *)

Lemma lt_iff_add p q : p < q <-> exists r, p + r = q.
Proof.
 unfold "<". rewrite <- sub_mask_neg_iff, compare_sub_mask.
 destruct sub_mask; now split.
Qed.

Lemma gt_iff_add p q : p > q <-> exists r, q + r = p.
Proof.
 unfold ">". rewrite compare_sub_mask.
 split.
 case_eq (sub_mask p q); try discriminate; intros r Hr _.
  exists r. now apply sub_mask_pos_iff.
 intros (r,Hr). apply sub_mask_pos_iff in Hr. now rewrite Hr.
Qed.

(** Basic facts about [compare_cont] *)

Theorem compare_cont_refl p c :
  compare_cont c p p = c.
Proof.
  now induction p.
Qed.

Lemma compare_cont_antisym p q c :
  CompOpp (compare_cont c p q) = compare_cont (CompOpp c) q p.
Proof.
  revert q c.
  induction p as [p IHp|p IHp| ]; intros [q|q| ] c; simpl;
   trivial; apply IHp.
Qed.

(** Basic facts about [compare] *)

Lemma compare_eq_iff p q : (p ?= q) = Eq <-> p = q.
Proof.
 rewrite compare_sub_mask, <- sub_mask_nul_iff.
 destruct sub_mask; now split.
Qed.

Lemma compare_antisym p q : (q ?= p) = CompOpp (p ?= q).
Proof.
  unfold compare. now rewrite compare_cont_antisym.
Qed.

Lemma compare_lt_iff p q : (p ?= q) = Lt <-> p < q.
Proof. reflexivity. Qed.

Lemma compare_le_iff p q : (p ?= q) <> Gt <-> p <= q.
Proof. reflexivity. Qed.

(** More properties about [compare] and boolean comparisons,
  including [compare_spec] and [lt_irrefl] and [lt_eq_cases]. *)

Include BoolOrderFacts.

Definition le_lteq := lt_eq_cases.

(** ** Facts about [gt] and [ge] *)

(** The predicates [lt] and [le] are now favored in the statements
  of theorems, the use of [gt] and [ge] is hence not recommended.
  We provide here the bare minimal results to related them with
  [lt] and [le]. *)

Lemma gt_lt_iff p q : p > q <-> q < p.
Proof.
 unfold lt, gt. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma gt_lt p q : p > q -> q < p.
Proof.
 apply gt_lt_iff.
Qed.

Lemma lt_gt p q : p < q -> q > p.
Proof.
 apply gt_lt_iff.
Qed.

Lemma ge_le_iff p q : p >= q <-> q <= p.
Proof.
 unfold le, ge. now rewrite compare_antisym, CompOpp_iff.
Qed.

Lemma ge_le p q : p >= q -> q <= p.
Proof.
 apply ge_le_iff.
Qed.

Lemma le_ge p q : p <= q -> q >= p.
Proof.
 apply ge_le_iff.
Qed.

(** ** Comparison and the successor *)

Lemma compare_succ_r p q :
  switch_Eq Gt (p ?= succ q) = switch_Eq Lt (p ?= q).
Proof.
  revert q.
  induction p as [p IH|p IH| ]; intros [q|q| ]; simpl;
   simpl_compare; rewrite ?IH; trivial;
   (now destruct compare) || (now destruct p).
Qed.

Lemma compare_succ_l p q :
  switch_Eq Lt (succ p ?= q) = switch_Eq Gt (p ?= q).
Proof.
  rewrite 2 (compare_antisym q). generalize (compare_succ_r q p).
  now do 2 destruct compare.
Qed.

Theorem lt_succ_r p q : p < succ q <-> p <= q.
Proof.
  unfold lt, le. generalize (compare_succ_r p q).
  do 2 destruct compare; try discriminate; now split.
Qed.

Lemma lt_succ_diag_r p : p < succ p.
Proof.
 rewrite lt_iff_add. exists 1. apply add_1_r.
Qed.

Lemma compare_succ_succ p q : (succ p ?= succ q) = (p ?= q).
Proof.
 revert q.
 induction p; destruct q; simpl; simpl_compare; trivial;
  apply compare_succ_l || apply compare_succ_r ||
  (now destruct p) || (now destruct q).
Qed.

(** ** 1 is the least positive number *)

Lemma le_1_l p : 1 <= p.
Proof.
  now destruct p.
Qed.

Lemma nlt_1_r p : ~ p < 1.
Proof.
  now destruct p.
Qed.

Lemma lt_1_succ p : 1 < succ p.
Proof.
  apply lt_succ_r, le_1_l.
Qed.

(** ** Properties of the order *)

Lemma le_nlt p q : p <= q <-> ~ q < p.
Proof.
  now rewrite <- ge_le_iff.
Qed.

Lemma lt_nle p q : p < q <-> ~ q <= p.
Proof.
 intros. unfold lt, le. rewrite compare_antisym.
 destruct compare; split; auto; easy'.
Qed.

Lemma lt_le_incl p q : p<q -> p<=q.
Proof.
  intros. apply le_lteq. now left.
Qed.

Lemma lt_lt_succ n m : n < m -> n < succ m.
Proof.
  intros. now apply lt_succ_r, lt_le_incl.
Qed.

Lemma succ_lt_mono n m : n < m <-> succ n < succ m.
Proof.
  unfold lt. now rewrite compare_succ_succ.
Qed.

Lemma succ_le_mono n m : n <= m <-> succ n <= succ m.
Proof.
  unfold le. now rewrite compare_succ_succ.
Qed.

Lemma lt_trans n m p : n < m -> m < p -> n < p.
Proof.
 rewrite 3 lt_iff_add. intros (r,Hr) (s,Hs).
 exists (r+s). now rewrite add_assoc, Hr, Hs.
Qed.

Theorem lt_ind : forall (A : positive -> Prop) (n : positive),
  A (succ n) ->
    (forall m : positive, n < m -> A m -> A (succ m)) ->
      forall m : positive, n < m -> A m.
Proof.
  intros A n AB AS m. induction m using peano_ind; intros H.
  elim (nlt_1_r _ H).
  apply lt_succ_r, le_lteq in H. destruct H as [H|H]; subst; auto.
Qed.

Instance lt_strorder : StrictOrder lt.
Proof. split. exact lt_irrefl. exact lt_trans. Qed.

Instance lt_compat : Proper (Logic.eq==>Logic.eq==>iff) lt.
Proof. repeat red. intros. subst; auto. Qed.

Lemma lt_total p q : p < q \/ p = q \/ q < p.
Proof.
 case (compare_spec p q); intuition.
Qed.

Lemma le_refl p : p <= p.
Proof.
 intros. unfold le. now rewrite compare_refl.
Qed.

Lemma le_lt_trans n m p : n <= m -> m < p -> n < p.
Proof.
 intros H H'. apply le_lteq in H. destruct H.
 now apply lt_trans with m. now subst.
Qed.

Lemma lt_le_trans n m p : n < m -> m <= p -> n < p.
Proof.
 intros H H'. apply le_lteq in H'. destruct H'.
 now apply lt_trans with m. now subst.
Qed.

Lemma le_trans n m p : n <= m -> m <= p -> n <= p.
Proof.
 intros H H'.
 apply le_lteq in H. destruct H.
 apply le_lteq; left. now apply lt_le_trans with m.
 now subst.
Qed.

Lemma le_succ_l n m : succ n <= m <-> n < m.
Proof.
 rewrite <- lt_succ_r. symmetry. apply succ_lt_mono.
Qed.

Lemma le_antisym p q : p <= q -> q <= p -> p = q.
Proof.
 rewrite le_lteq; destruct 1; auto.
 rewrite le_lteq; destruct 1; auto.
 elim (lt_irrefl p). now transitivity q.
Qed.

Instance le_preorder : PreOrder le.
Proof. split. exact le_refl. exact le_trans. Qed.

Instance le_partorder : PartialOrder Logic.eq le.
Proof.
 intros x y. change (x=y <-> x <= y <= x).
 split. intros; now subst.
 destruct 1; now apply le_antisym.
Qed.

(** ** Comparison and addition *)

Lemma add_compare_mono_l p q r : (p+q ?= p+r) = (q ?= r).
Proof.
 revert p q r. induction p using peano_ind; intros q r.
 rewrite 2 add_1_l. apply compare_succ_succ.
 now rewrite 2 add_succ_l, compare_succ_succ.
Qed.

Lemma add_compare_mono_r p q r : (q+p ?= r+p) = (q ?= r).
Proof.
 rewrite 2 (add_comm _ p). apply add_compare_mono_l.
Qed.

(** ** Order and addition *)

Lemma lt_add_diag_r p q : p < p + q.
Proof.
 rewrite lt_iff_add. now exists q.
Qed.

Lemma add_lt_mono_l p q r : q<r <-> p+q < p+r.
Proof.
 unfold lt. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_lt_mono_r p q r : q<r <-> q+p < r+p.
Proof.
 unfold lt. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_lt_mono p q r s : p<q -> r<s -> p+r<q+s.
Proof.
 intros. apply lt_trans with (p+s).
 now apply add_lt_mono_l.
 now apply add_lt_mono_r.
Qed.

Lemma add_le_mono_l p q r : q<=r <-> p+q<=p+r.
Proof.
 unfold le. rewrite add_compare_mono_l. apply iff_refl.
Qed.

Lemma add_le_mono_r p q r : q<=r <-> q+p<=r+p.
Proof.
 unfold le. rewrite add_compare_mono_r. apply iff_refl.
Qed.

Lemma add_le_mono p q r s : p<=q -> r<=s -> p+r <= q+s.
Proof.
 intros. apply le_trans with (p+s).
 now apply add_le_mono_l.
 now apply add_le_mono_r.
Qed.

(** ** Comparison and multiplication *)

Lemma mul_compare_mono_l p q r : (p*q ?= p*r) = (q ?= r).
Proof.
 revert q r. induction p; simpl; trivial.
 intros q r. specialize (IHp q r).
 destruct (compare_spec q r).
 subst. apply compare_refl.
 now apply add_lt_mono.
 now apply lt_gt, add_lt_mono, gt_lt.
Qed.

Lemma mul_compare_mono_r p q r : (q*p ?= r*p) = (q ?= r).
Proof.
 rewrite 2 (mul_comm _ p). apply mul_compare_mono_l.
Qed.

(** ** Order and multiplication *)

Lemma mul_lt_mono_l p q r : q<r <-> p*q < p*r.
Proof.
 unfold lt. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_lt_mono_r p q r : q<r <-> q*p < r*p.
Proof.
 unfold lt. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_lt_mono p q r s : p<q -> r<s -> p*r < q*s.
Proof.
 intros. apply lt_trans with (p*s).
 now apply mul_lt_mono_l.
 now apply mul_lt_mono_r.
Qed.

Lemma mul_le_mono_l p q r : q<=r <-> p*q<=p*r.
Proof.
 unfold le. rewrite mul_compare_mono_l. apply iff_refl.
Qed.

Lemma mul_le_mono_r p q r : q<=r <-> q*p<=r*p.
Proof.
 unfold le. rewrite mul_compare_mono_r. apply iff_refl.
Qed.

Lemma mul_le_mono p q r s : p<=q -> r<=s -> p*r <= q*s.
Proof.
 intros. apply le_trans with (p*s).
 now apply mul_le_mono_l.
 now apply mul_le_mono_r.
Qed.

Lemma lt_add_r p q : p < p+q.
Proof.
 induction q using peano_ind.
 rewrite add_1_r. apply lt_succ_diag_r.
 apply lt_trans with (p+q); auto.
 apply add_lt_mono_l, lt_succ_diag_r.
Qed.

Lemma lt_not_add_l p q : ~ p+q < p.
Proof.
 intro H. elim (lt_irrefl p).
 apply lt_trans with (p+q); auto using lt_add_r.
Qed.

Lemma pow_gt_1 n p : 1<n -> 1<n^p.
Proof.
 intros H. induction p using peano_ind.
 now rewrite pow_1_r.
 rewrite pow_succ_r.
 apply lt_trans with (n*1).
 now rewrite mul_1_r.
 now apply mul_lt_mono_l.
Qed.

(**********************************************************************)
(** * Properties of subtraction on binary positive numbers *)

Lemma sub_1_r p : sub p 1 = pred p.
Proof.
  now destruct p.
Qed.

Lemma pred_sub p : pred p = sub p 1.
Proof.
  symmetry. apply sub_1_r.
Qed.

Theorem sub_succ_r p q : p - (succ q) = pred (p - q).
Proof.
  unfold sub; rewrite sub_mask_succ_r, sub_mask_carry_spec.
  destruct (sub_mask p q) as [|[r|r| ]|]; auto.
Qed.

(** ** Properties of subtraction without underflow *)

Lemma sub_mask_pos' p q :
  q < p -> exists r, sub_mask p q = IsPos r /\ q + r = p.
Proof.
 rewrite lt_iff_add. intros (r,Hr). exists r. split; trivial.
 now apply sub_mask_pos_iff.
Qed.

Lemma sub_mask_pos p q :
  q < p -> exists r, sub_mask p q = IsPos r.
Proof.
 intros H. destruct (sub_mask_pos' p q H) as (r & Hr & _). now exists r.
Qed.

Theorem sub_add p q : q < p -> (p-q)+q = p.
Proof.
  intros H. destruct (sub_mask_pos p q H) as (r,U).
  unfold sub. rewrite U. rewrite add_comm. now apply sub_mask_add.
Qed.

Lemma add_sub p q : (p+q)-q = p.
Proof.
 intros. apply add_reg_r with q.
 rewrite sub_add; trivial.
 rewrite add_comm. apply lt_add_r.
Qed.

Lemma mul_sub_distr_l p q r : r<q -> p*(q-r) = p*q-p*r.
Proof.
 intros H.
 apply add_reg_r with (p*r).
 rewrite <- mul_add_distr_l.
 rewrite sub_add; trivial.
 symmetry. apply sub_add; trivial.
 now apply mul_lt_mono_l.
Qed.

Lemma mul_sub_distr_r p q r : q<p -> (p-q)*r = p*r-q*r.
Proof.
 intros H. rewrite 3 (mul_comm _ r). now apply mul_sub_distr_l.
Qed.

Lemma sub_lt_mono_l p q r: q<p -> p<r -> r-p < r-q.
Proof.
 intros Hqp Hpr.
 apply (add_lt_mono_r p).
 rewrite sub_add by trivial.
 apply le_lt_trans with ((r-q)+q).
 rewrite sub_add by (now apply lt_trans with p).
 apply le_refl.
 now apply add_lt_mono_l.
Qed.

Lemma sub_compare_mono_l p q r :
 q<p -> r<p -> (p-q ?= p-r) = (r ?= q).
Proof.
 intros Hqp Hrp.
 case (compare_spec r q); intros H. subst. apply compare_refl.
 apply sub_lt_mono_l; trivial.
 apply lt_gt, sub_lt_mono_l; trivial.
Qed.

Lemma sub_compare_mono_r p q r :
 p<q -> p<r -> (q-p ?= r-p) = (q ?= r).
Proof.
 intros. rewrite <- (add_compare_mono_r p), 2 sub_add; trivial.
Qed.

Lemma sub_lt_mono_r p q r : q<p -> r<q -> q-r < p-r.
Proof.
 intros. unfold lt. rewrite sub_compare_mono_r; trivial.
 now apply lt_trans with q.
Qed.

Lemma sub_decr n m : m<n -> n-m < n.
Proof.
 intros.
 apply add_lt_mono_r with m.
 rewrite sub_add; trivial.
 apply lt_add_r.
Qed.

Lemma add_sub_assoc p q r : r<q -> p+(q-r) = p+q-r.
Proof.
 intros.
 apply add_reg_r with r.
 rewrite <- add_assoc, !sub_add; trivial.
 rewrite add_comm. apply lt_trans with q; trivial using lt_add_r.
Qed.

Lemma sub_add_distr p q r : q+r < p -> p-(q+r) = p-q-r.
Proof.
 intros.
 assert (q < p)
  by (apply lt_trans with (q+r); trivial using lt_add_r).
 rewrite (add_comm q r) in *.
 apply add_reg_r with (r+q).
 rewrite sub_add by trivial.
 rewrite add_assoc, !sub_add; trivial.
 apply (add_lt_mono_r q). rewrite sub_add; trivial.
Qed.

Lemma sub_sub_distr p q r : r<q -> q-r < p -> p-(q-r) = p+r-q.
Proof.
 intros.
 apply add_reg_r with ((q-r)+r).
 rewrite add_assoc, !sub_add; trivial.
 rewrite <- (sub_add q r); trivial.
 now apply add_lt_mono_r.
Qed.

(** Recursive equations for [sub] *)

Lemma sub_xO_xO n m : m<n -> n~0 - m~0 = (n-m)~0.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xI n m : m<n -> n~1 - m~1 = (n-m)~0.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m H) as (p, ->).
Qed.

Lemma sub_xI_xO n m : m<n -> n~1 - m~0 = (n-m)~1.
Proof.
 intros H. unfold sub. simpl.
 now destruct (sub_mask_pos n m) as (p, ->).
Qed.

Lemma sub_xO_xI n m : n~0 - m~1 = pred_double (n-m).
Proof.
 unfold sub. simpl. rewrite sub_mask_carry_spec.
 now destruct (sub_mask n m) as [|[r|r|]|].
Qed.

(** Properties of subtraction with underflow *)

Lemma sub_mask_neg_iff' p q : sub_mask p q = IsNeg <-> p < q.
Proof.
  rewrite lt_iff_add. apply sub_mask_neg_iff.
Qed.

Lemma sub_mask_neg p q : p<q -> sub_mask p q = IsNeg.
Proof.
  apply sub_mask_neg_iff'.
Qed.

Lemma sub_le p q : p<=q -> p-q = 1.
Proof.
  unfold le, sub. rewrite compare_sub_mask.
  destruct sub_mask; easy'.
Qed.

Lemma sub_lt p q : p<q -> p-q = 1.
Proof.
  intros. now apply sub_le, lt_le_incl.
Qed.

Lemma sub_diag p : p-p = 1.
Proof.
  unfold sub. now rewrite sub_mask_diag.
Qed.

(** ** Results concerning [size] and [size_nat] *)

Lemma size_nat_monotone p q : p<q -> (size_nat p <= size_nat q)%nat.
Proof.
  assert (le0 : forall n, (0<=n)%nat) by (induction n; auto).
  assert (leS : forall n m, (n<=m -> S n <= S m)%nat) by (induction 1; auto).
  revert q.
  induction p; destruct q; simpl; intros; auto; easy || apply leS;
   red in H; simpl_compare_in H.
  apply IHp. red. now destruct (p?=q).
  destruct (compare_spec p q); subst; now auto.
Qed.

Lemma size_gt p : p < 2^(size p).
Proof.
 induction p; simpl; try rewrite pow_succ_r; try easy.
 apply le_succ_l in IHp. now apply le_succ_l.
Qed.

Lemma size_le p : 2^(size p) <= p~0.
Proof.
 induction p; simpl; try rewrite pow_succ_r; try easy.
 apply mul_le_mono_l.
 apply le_lteq; left. rewrite xI_succ_xO. apply lt_succ_r, IHp.
Qed.

(** ** Properties of [min] and [max] *)

(** First, the specification *)

Lemma max_l : forall x y, y<=x -> max x y = x.
Proof.
 intros x y H. unfold max. case compare_spec; auto.
 intros H'. apply le_nlt in H. now elim H.
Qed.

Lemma max_r : forall x y, x<=y -> max x y = y.
Proof.
 unfold le, max. intros x y. destruct compare; easy'.
Qed.

Lemma min_l : forall x y, x<=y -> min x y = x.
Proof.
 unfold le, min. intros x y. destruct compare; easy'.
Qed.

Lemma min_r : forall x y, y<=x -> min x y = y.
Proof.
 intros x y H. unfold min. case compare_spec; auto.
 intros H'. apply le_nlt in H. now elim H'.
Qed.

(** We hence obtain all the generic properties of [min] and [max]. *)

Include UsualMinMaxLogicalProperties <+ UsualMinMaxDecProperties.

Ltac order := Private_Tac.order.

(** Minimum, maximum and constant one *)

Lemma max_1_l n : max 1 n = n.
Proof.
 unfold max. case compare_spec; auto.
 intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma max_1_r n : max n 1 = n.
Proof. rewrite max_comm. apply max_1_l. Qed.

Lemma min_1_l n : min 1 n = 1.
Proof.
 unfold min. case compare_spec; auto.
 intros H. apply lt_nle in H. elim H. apply le_1_l.
Qed.

Lemma min_1_r n : min n 1 = 1.
Proof. rewrite min_comm. apply min_1_l. Qed.

(** Minimum, maximum and operations (consequences of monotonicity) *)

Lemma succ_max_distr n m : succ (max n m) = max (succ n) (succ m).
Proof.
 symmetry. apply max_monotone.
 intros x x'. apply succ_le_mono.
Qed.

Lemma succ_min_distr n m : succ (min n m) = min (succ n) (succ m).
Proof.
 symmetry. apply min_monotone.
 intros x x'. apply succ_le_mono.
Qed.

Lemma add_max_distr_l n m p : max (p + n) (p + m) = p + max n m.
Proof.
 apply max_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_max_distr_r n m p : max (n + p) (m + p) = max n m + p.
Proof.
 rewrite 3 (add_comm _ p). apply add_max_distr_l.
Qed.

Lemma add_min_distr_l n m p : min (p + n) (p + m) = p + min n m.
Proof.
 apply min_monotone. intros x x'. apply add_le_mono_l.
Qed.

Lemma add_min_distr_r n m p : min (n + p) (m + p) = min n m + p.
Proof.
 rewrite 3 (add_comm _ p). apply add_min_distr_l.
Qed.

Lemma mul_max_distr_l n m p : max (p * n) (p * m) = p * max n m.
Proof.
 apply max_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_max_distr_r n m p : max (n * p) (m * p) = max n m * p.
Proof.
 rewrite 3 (mul_comm _ p). apply mul_max_distr_l.
Qed.

Lemma mul_min_distr_l n m p : min (p * n) (p * m) = p * min n m.
Proof.
 apply min_monotone. intros x x'. apply mul_le_mono_l.
Qed.

Lemma mul_min_distr_r n m p : min (n * p) (m * p) = min n m * p.
Proof.
 rewrite 3 (mul_comm _ p). apply mul_min_distr_l.
Qed.


(** ** Results concerning [iter_op] *)

Lemma iter_op_succ : forall A (op:A->A->A),
 (forall x y z, op x (op y z) = op (op x y) z) ->
 forall p a,
 iter_op op (succ p) a = op a (iter_op op p a).
Proof.
 induction p; simpl; intros; trivial.
 rewrite H. apply IHp.
Qed.

(** ** Results about [of_nat] and [of_succ_nat] *)

Lemma of_nat_succ (n:nat) : of_succ_nat n = of_nat (S n).
Proof.
 induction n. trivial. simpl. f_equal. now rewrite IHn.
Qed.

Lemma pred_of_succ_nat (n:nat) : pred (of_succ_nat n) = of_nat n.
Proof.
 destruct n. trivial. simpl pred. rewrite pred_succ. apply of_nat_succ.
Qed.

Lemma succ_of_nat (n:nat) : n<>O -> succ (of_nat n) = of_succ_nat n.
Proof.
 rewrite of_nat_succ. destruct n; trivial. now destruct 1.
Qed.

(** ** Correctness proofs for the square root function *)

Inductive SqrtSpec : positive*mask -> positive -> Prop :=
 | SqrtExact s x : x=s*s -> SqrtSpec (s,IsNul) x
 | SqrtApprox s r x : x=s*s+r -> r <= s~0 -> SqrtSpec (s,IsPos r) x.

Lemma sqrtrem_step_spec f g p x :
 (f=xO \/ f=xI) -> (g=xO \/ g=xI) ->
 SqrtSpec p x -> SqrtSpec (sqrtrem_step f g p) (g (f x)).
Proof.
intros Hf Hg [ s _ -> | s r _ -> Hr ].
(* exact *)
unfold sqrtrem_step.
destruct Hf,Hg; subst; simpl; constructor; now rewrite ?square_xO.
(* approx *)
assert (Hfg : forall p q, g (f (p+q)) = p~0~0 + g (f q))
 by (intros; destruct Hf, Hg; now subst).
unfold sqrtrem_step, leb.
case compare_spec; [intros EQ | intros LT | intros GT].
(* - EQ *)
rewrite <- EQ, sub_mask_diag. constructor.
destruct Hg; subst g; destr_eq EQ.
destruct Hf; subst f; destr_eq EQ.
subst. now rewrite square_xI.
(* - LT *)
destruct (sub_mask_pos' _ _ LT) as (y & -> & H). constructor.
rewrite Hfg, <- H. now rewrite square_xI, add_assoc. clear Hfg.
rewrite <- lt_succ_r in Hr. change (r < s~1) in Hr.
rewrite <- lt_succ_r, (add_lt_mono_l (s~0~1)), H. simpl.
rewrite add_carry_spec, add_diag. simpl.
destruct Hf,Hg; subst; red; simpl_compare; now rewrite Hr.
(* - GT *)
constructor. now rewrite Hfg, square_xO. apply lt_succ_r, GT.
Qed.

Lemma sqrtrem_spec p : SqrtSpec (sqrtrem p) p.
Proof.
revert p. fix 1.
 destruct p; try destruct p; try (constructor; easy);
  apply sqrtrem_step_spec; auto.
Qed.

Lemma sqrt_spec p :
 let s := sqrt p in s*s <= p < (succ s)*(succ s).
Proof.
 simpl.
 assert (H:=sqrtrem_spec p).
 unfold sqrt in *. destruct sqrtrem as (s,rm); simpl.
 inversion_clear H; subst.
 (* exact *)
 split. reflexivity. apply mul_lt_mono; apply lt_succ_diag_r.
 (* approx *)
 split.
 apply lt_le_incl, lt_add_r.
 rewrite <- add_1_l, mul_add_distr_r, !mul_add_distr_l, !mul_1_r, !mul_1_l.
 rewrite add_assoc, (add_comm _ r). apply add_lt_mono_r.
 now rewrite <- add_assoc, add_diag, add_1_l, lt_succ_r.
Qed.

(** ** Correctness proofs for the gcd function *)

Lemma divide_add_cancel_l p q r : (p | r) -> (p | q + r) -> (p | q).
Proof.
 intros (s,Hs) (t,Ht).
 exists (t-s).
 rewrite mul_sub_distr_r.
 rewrite <- Hs, <- Ht.
 symmetry. apply add_sub.
 apply mul_lt_mono_r with p.
 rewrite <- Hs, <- Ht, add_comm.
 apply lt_add_r.
Qed.

Lemma divide_xO_xI p q r : (p | q~0) -> (p | r~1) -> (p | q).
Proof.
 intros (s,Hs) (t,Ht).
 destruct p.
 destruct s; try easy. simpl in Hs. destr_eq Hs. now exists s.
 rewrite mul_xO_r in Ht; discriminate.
 exists q; now rewrite mul_1_r.
Qed.

Lemma divide_xO_xO p q : (p~0|q~0) <-> (p|q).
Proof.
 split; intros (r,H); simpl in *.
 rewrite mul_xO_r in H. destr_eq H. now exists r.
 exists r; simpl. rewrite mul_xO_r. f_equal; auto.
Qed.

Lemma divide_mul_l p q r : (p|q) -> (p|q*r).
Proof.
 intros (s,H). exists (s*r).
 rewrite <- mul_assoc, (mul_comm r p), mul_assoc. now f_equal.
Qed.

Lemma divide_mul_r p q r : (p|r) -> (p|q*r).
Proof.
 rewrite mul_comm. apply divide_mul_l.
Qed.

(** The first component of ggcd is gcd *)

Lemma ggcdn_gcdn : forall n a b,
  fst (ggcdn n a b) = gcdn n a b.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case compare_spec; simpl; trivial;
  rewrite <- IHn; destruct ggcdn as (g,(u,v)); simpl; auto.
Qed.

Lemma ggcd_gcd : forall a b, fst (ggcd a b) = gcd a b.
Proof.
 unfold ggcd, gcd. intros. apply ggcdn_gcdn.
Qed.

(** The other components of ggcd are indeed the correct factors. *)

Ltac destr_pggcdn IHn :=
 match goal with |- context [ ggcdn _ ?x ?y ] =>
  generalize (IHn x y); destruct ggcdn as (g,(u,v)); simpl
 end.

Lemma ggcdn_correct_divisors : forall n a b,
  let '(g,(aa,bb)) := ggcdn n a b in
  a = g*aa /\ b = g*bb.
Proof.
 induction n.
 simpl; auto.
 destruct a, b; simpl; auto; try case compare_spec; try destr_pggcdn IHn.
 (* Eq *)
 intros ->. now rewrite mul_comm.
 (* Lt *)
 intros (H',H) LT; split; auto.
 rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 rewrite add_comm. now apply sub_add.
 (* Gt *)
 intros (H',H) LT; split; auto.
 rewrite mul_add_distr_l, mul_xO_r, <- H, <- H'.
 simpl. f_equal. symmetry.
 rewrite add_comm. now apply sub_add.
 (* Then... *)
 intros (H,H'); split; auto. rewrite mul_xO_r, H'; auto.
 intros (H,H'); split; auto. rewrite mul_xO_r, H; auto.
 intros (H,H'); split; subst; auto.
Qed.

Lemma ggcd_correct_divisors : forall a b,
  let '(g,(aa,bb)) := ggcd a b in
  a=g*aa /\ b=g*bb.
Proof.
 unfold ggcd. intros. apply ggcdn_correct_divisors.
Qed.

(** We can use this fact to prove a part of the gcd correctness *)

Lemma gcd_divide_l : forall a b, (gcd a b | a).
Proof.
 intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (H,_). exists aa.
  now rewrite mul_comm.
Qed.

Lemma gcd_divide_r : forall a b, (gcd a b | b).
Proof.
 intros a b. rewrite <- ggcd_gcd. generalize (ggcd_correct_divisors a b).
 destruct ggcd as (g,(aa,bb)); simpl. intros (_,H). exists bb.
  now rewrite mul_comm.
Qed.

(** We now prove directly that gcd is the greatest amongst common divisors *)

Lemma gcdn_greatest : forall n a b, (size_nat a + size_nat b <= n)%nat ->
 forall p, (p|a) -> (p|b) -> (p|gcdn n a b).
Proof.
 induction n.
 destruct a, b; simpl; inversion 1.
 destruct a, b; simpl; try case compare_spec; simpl; auto.
 (* Lt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
 rewrite plus_comm, <- plus_n_Sm, <- plus_Sn_m.
 apply plus_le_compat; trivial.
 apply size_nat_monotone, sub_decr, LT.
 apply divide_xO_xI with a; trivial.
 apply (divide_add_cancel_l p _ a~1); trivial.
 now rewrite <- sub_xI_xI, sub_add.
 (* Gt *)
 intros LT LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. eapply Le.le_trans; [|eapply LE].
 apply plus_le_compat; trivial.
 apply size_nat_monotone, sub_decr, LT.
 apply divide_xO_xI with b; trivial.
 apply (divide_add_cancel_l p _ b~1); trivial.
 now rewrite <- sub_xI_xI, sub_add.
 (* a~1 b~0 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 apply le_S_n in LE. simpl. now rewrite plus_n_Sm.
 apply divide_xO_xI with a; trivial.
 (* a~0 b~1 *)
 intros LE p Hp1 Hp2. apply IHn; clear IHn; trivial.
 simpl. now apply le_S_n.
 apply divide_xO_xI with b; trivial.
 (* a~0 b~0 *)
 intros LE p Hp1 Hp2.
 destruct p.
 change (gcdn n a b)~0 with (2*(gcdn n a b)).
 apply divide_mul_r.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 apply divide_xO_xI with p; trivial. now exists 1.
 apply divide_xO_xI with p; trivial. now exists 1.
 apply divide_xO_xO.
 apply IHn; clear IHn.
 apply le_S_n in LE. apply le_Sn_le. now rewrite plus_n_Sm.
 now apply divide_xO_xO.
 now apply divide_xO_xO.
 exists (gcdn n a b)~0. now rewrite mul_1_r.
Qed.

Lemma gcd_greatest : forall a b p, (p|a) -> (p|b) -> (p|gcd a b).
Proof.
 intros. apply gcdn_greatest; auto.
Qed.

(** As a consequence, the rests after division by gcd are relatively prime *)

Lemma ggcd_greatest : forall a b,
 let (aa,bb) := snd (ggcd a b) in
 forall p, (p|aa) -> (p|bb) -> p=1.
Proof.
 intros. generalize (gcd_greatest a b) (ggcd_correct_divisors a b).
 rewrite <- ggcd_gcd. destruct ggcd as (g,(aa,bb)); simpl.
 intros H (EQa,EQb) p Hp1 Hp2; subst.
 assert (H' : (g*p | g)).
  apply H.
  destruct Hp1 as (r,Hr). exists r.
   now rewrite mul_assoc, (mul_comm r g), <- mul_assoc, <- Hr.
  destruct Hp2 as (r,Hr). exists r.
   now rewrite mul_assoc, (mul_comm r g), <- mul_assoc, <- Hr.
 destruct H' as (q,H').
 rewrite (mul_comm g p), mul_assoc in H'.
 apply mul_eq_1 with q; rewrite mul_comm.
 now apply mul_reg_r with g.
Qed.

End Pos.

Bind Scope positive_scope with Pos.t positive.

(** Exportation of notations *)

Infix "+" := Pos.add : positive_scope.
Infix "-" := Pos.sub : positive_scope.
Infix "*" := Pos.mul : positive_scope.
Infix "^" := Pos.pow : positive_scope.
Infix "?=" := Pos.compare (at level 70, no associativity) : positive_scope.
Infix "=?" := Pos.eqb (at level 70, no associativity) : positive_scope.
Infix "<=?" := Pos.leb (at level 70, no associativity) : positive_scope.
Infix "<?" := Pos.ltb (at level 70, no associativity) : positive_scope.
Infix "<=" := Pos.le : positive_scope.
Infix "<" := Pos.lt : positive_scope.
Infix ">=" := Pos.ge : positive_scope.
Infix ">" := Pos.gt : positive_scope.

Notation "x <= y <= z" := (x <= y /\ y <= z) : positive_scope.
Notation "x <= y < z" := (x <= y /\ y < z) : positive_scope.
Notation "x < y < z" := (x < y /\ y < z) : positive_scope.
Notation "x < y <= z" := (x < y /\ y <= z) : positive_scope.

Notation "( p | q )" := (Pos.divide p q) (at level 0) : positive_scope.

(** More complex compatibility facts, expressed as lemmas
    (to preserve scopes for instance) *)

Lemma Peqb_true_eq x y : Pos.eqb x y = true -> x=y.
Proof. apply Pos.eqb_eq. Qed.
Lemma Pcompare_eq_Gt p q : (p ?= q) = Gt <-> p > q.
Proof. reflexivity. Qed.
Lemma Pplus_one_succ_r p : Pos.succ p = p + 1.
Proof (eq_sym (Pos.add_1_r p)).
Lemma Pplus_one_succ_l p : Pos.succ p = 1 + p.
Proof (eq_sym (Pos.add_1_l p)).
Lemma Pcompare_refl p : Pos.compare_cont Eq p p = Eq.
Proof (Pos.compare_cont_refl p Eq).
Lemma Pcompare_Eq_eq : forall p q, Pos.compare_cont Eq p q = Eq -> p = q.
Proof Pos.compare_eq.
Lemma ZC4 p q : Pos.compare_cont Eq p q = CompOpp (Pos.compare_cont Eq q p).
Proof (Pos.compare_antisym q p).
Lemma Ppred_minus p : Pos.pred p = p - 1.
Proof (eq_sym (Pos.sub_1_r p)).

Lemma Pminus_mask_Gt p q :
  p > q ->
  exists h : positive,
   Pos.sub_mask p q = IsPos h /\
   q + h = p /\ (h = 1 \/ Pos.sub_mask_carry p q = IsPos (Pos.pred h)).
Proof.
 intros H. apply Pos.gt_lt in H.
 destruct (Pos.sub_mask_pos p q H) as (r & U).
 exists r. repeat split; trivial.
 now apply Pos.sub_mask_pos_iff.
 destruct (Pos.eq_dec r 1) as [EQ|NE]; [now left|right].
 rewrite Pos.sub_mask_carry_spec, U. destruct r; trivial. now elim NE.
Qed.

Lemma Pplus_minus : forall p q, p > q -> q+(p-q) = p.
Proof.
 intros. rewrite Pos.add_comm. now apply Pos.sub_add, Pos.gt_lt.
Qed.
 *)