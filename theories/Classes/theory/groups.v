Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C f g.

(** ** Equations for an explicit operation *)

(** The following lemmas take the operation as an explicit argument, rather than using [sg_op], so that they can be used to rewrite with operations such as [plus] and [mult], e.g., [rewrite (swap_middle (+))]. The group lemmas assume [IsGroup] rather than the individual laws they use: on a concrete ring such as the field of fractions, typeclass search for a single law such as [Associative plus] can unfold [plus] to its definition, while [IsGroup] is found directly. *)

Lemma swap_middle {A} (op : A -> A -> A) `{!Associative op, !Commutative op}
  (a b c d : A)
  : op (op a b) (op c d) = op (op a c) (op b d).
Proof.
  rewrite <- !(simple_associativity (f:=op)).
  apply ap.
  rewrite !(simple_associativity (f:=op)).
  apply (ap (fun w => op w d)), commutativity.
Qed.

(** Cancelling a left inverse [op (inv y) y]. *)
Lemma left_inverse_cancel {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsGroup A op unit inv} (x y : A)
  : op (op x (inv y)) y = x.
Proof.
  exact ((simple_associativity x (inv y) y)^ @ ap (op x) (left_inverse y) @ right_identity x).
Defined.

(** Cancelling a right inverse [op y (inv y)]. *)
Lemma right_inverse_cancel {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsGroup A op unit inv} (x y : A)
  : op (op x y) (inv y) = x.
Proof.
  exact ((simple_associativity x y (inv y))^ @ ap (op x) (right_inverse y) @ right_identity x).
Defined.

Lemma inverse_telescope {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsGroup A op unit inv} (x y z : A)
  : op (op x (inv y)) (op y (inv z)) = op x (inv z).
Proof.
  lhs rapply simple_associativity.
  exact (ap (fun w => op w (inv z)) (left_inverse_cancel op x y)).
Qed.

Section group_props.
  Context `{IsGroup G}.

  (** Group inverses are involutive *)
  #[export] Instance inverse_involutive : Involutive (^).
  Proof.
    intros x.
    transitivity (mon_unit * x).
    2: apply left_identity.
    transitivity ((x^^ *  x^) * x).
    2: apply (@ap _ _ (fun y => y * x)),
          left_inverse.
    transitivity (x^^ * (x^ * x)).
    2: apply associativity.
    transitivity (x^^ * mon_unit).
    2: apply ap, symmetry, left_inverse.
    apply symmetry, right_identity.
  Qed.

  #[export] Instance isinj_group_inverse : IsInjective (^).
  Proof.
    intros x y E.
    refine ((involutive x)^ @ _ @ involutive y).
    apply ap, E.
  Qed.

  Lemma inverse_mon_unit : mon_unit^ = mon_unit.
  Proof.
    change ((fun x => mon_unit^ = x) mon_unit).
    apply (transport _ (left_inverse mon_unit)).
    apply symmetry, right_identity.
  Qed.

  #[export] Instance group_cancelL : forall z : G, LeftCancellation (.*.) z.
  Proof.
    intros z x y E.
    rhs_V rapply left_identity.
    rhs_V exact (ap (.* y) (left_inverse z)).
    rhs_V rapply simple_associativity.
    rhs_V rapply (ap (-z *.) E).
    symmetry.
    lhs rapply simple_associativity.
    lhs exact (ap (.* x) (left_inverse z)).
    apply left_identity.
  Defined.

  #[export] Instance group_cancelR: forall z : G, RightCancellation (.*.) z.
  Proof.
    intros z x y E.
    rewrite <-(right_identity x).
    rewrite <-(right_inverse (unit:=mon_unit) z).
    rewrite associativity.
    rewrite E.
    rewrite <-(associativity y ), right_inverse, right_identity.
    reflexivity.
  Qed.

  Lemma inverse_sg_op x y : (x * y)^ = y^ * x^.
  Proof.
    rewrite <- (left_identity (-y * -x)).
    rewrite <- (left_inverse (unit:=mon_unit) (x * y)).
    rewrite <- simple_associativity.
    rewrite <- simple_associativity.
    rewrite (associativity y).
    rewrite right_inverse.
    rewrite (left_identity (-x)).
    rewrite right_inverse.
    apply symmetry, right_identity.
  Qed.

End group_props.

Section abgroup_props.
  Local Open Scope mc_add_scope.

  Lemma negate_sg_op_distr `{IsAbGroup G} x y : -(x + y) = -x + -y.
  Proof.
    path_via (-y + -x).
    - rapply inverse_sg_op.
    - apply commutativity.
  Qed.

  Local Close Scope mc_add_scope.
End abgroup_props.

(** In an abelian group, [(z + x) - (z + y) = x - y]. *)
Lemma common_left_cancel {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsAbGroup A op unit inv} (x y z : A)
  : op (op z x) (inv (op z y)) = op x (inv y).
Proof.
  lhs exact (ap (op (op z x)) (@negate_sg_op_distr A op unit inv _ z y)).
  lhs rapply swap_middle.
  lhs exact (ap (fun w => op w (op x (inv y))) (right_inverse z)).
  rapply left_identity.
Qed.

Section groupmor_props.

  Context `{IsGroup A} `{IsGroup B} {f : A -> B} `{!IsMonoidPreserving f}.

  Lemma preserves_inverse x : f x^ = (f x)^.
  Proof.
    apply (left_cancellation (.*.) (f x)).
    rewrite <-preserves_sg_op.
    rewrite 2!right_inverse.
    exact preserves_mon_unit.
  Qed.

End groupmor_props.

Section from_another_sg.

  Context
    `{IsSemiGroup A} `{IsHSet B}
    `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_sg: IsSemiGroup B.
  Proof.
  split.
  - exact _.
  - repeat intro; apply (injective f).
    rewrite !op_correct. apply associativity.
  Qed.
End from_another_sg.

Section from_another_com.

  Context `{SgOp A} `{!Commutative (A:=A) sg_op} {B}
   `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_comm : Commutative (A:=B) sg_op.
  Proof.
    intros x y.
    apply (injective f).
    rewrite 2!op_correct.
    apply commutativity.
  Qed.

End from_another_com.

Section from_another_com_sg.

  Context
    `{IsCommutativeSemiGroup A} `{IsHSet B}
    `{Bop : SgOp B} (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y).

  Lemma projected_com_sg : IsCommutativeSemiGroup B.
  Proof.
    split.
    - apply (projected_sg f);assumption.
    - apply (projected_comm f);assumption.
  Qed.

End from_another_com_sg.

Section from_another_monoid.

  Context `{IsMonoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y) (unit_correct : f mon_unit = mon_unit).

  Lemma projected_monoid : IsMonoid B.
  Proof.
    split.
    - apply (projected_sg f). assumption.
    - repeat intro; apply (injective f).
      rewrite op_correct, unit_correct, left_identity.
      reflexivity.
    - repeat intro; apply (injective f).
      rewrite op_correct, unit_correct, right_identity.
      reflexivity.
  Qed.

End from_another_monoid.

Section from_another_com_monoid.

  Context
   `{IsCommutativeMonoid A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x * y) = f x * f y)
   (unit_correct : f mon_unit = mon_unit).

  Lemma projected_com_monoid : IsCommutativeMonoid B.
  Proof.
    split.
    - apply (projected_monoid f);assumption.
    - apply (projected_comm f);assumption.
  Qed.

End from_another_com_monoid.

Section from_another_group.

  Context
    `{isg : IsGroup A} `{IsHSet B}
    `{Bop : SgOp B} `{Bunit : MonUnit B} `{Binv : Inverse B}
    (f : B -> A) `{!IsInjective f}
    (op_correct : forall x y, f (x * y) = f x * f y)
    (unit_correct : f mon_unit = mon_unit)
    (inverse_correct : forall x, f x^ = (f x)^).

  Lemma projected_group : IsGroup B.
  Proof.
    split.
    - apply (projected_monoid f);assumption.
    - repeat intro; apply (injective f).
      rewrite op_correct, inverse_correct, unit_correct, left_inverse.
      apply reflexivity.
    - repeat intro; apply (injective f).
      rewrite op_correct, inverse_correct, unit_correct, right_inverse.
      reflexivity.
  Qed.

End from_another_group.

Section from_another_ab_group.
  Local Open Scope mc_add_scope.

  Context `{IsAbGroup A} `{IsHSet B}
   `{Bop : SgOp B} `{Bunit : MonUnit B} `{Bnegate : Negate B}
   (f : B -> A) `{!IsInjective f}
   (op_correct : forall x y, f (x + y) = f x + f y)
   (unit_correct : f 0 = 0)
   (negate_correct : forall x, f (-x) = -f x).

  Lemma projected_ab_group : IsAbGroup B.
  Proof.
    split.
    - apply (projected_group f (isg:=abgroup_group _)); assumption.
    - apply (projected_comm f); assumption.
  Qed.

  Local Close Scope mc_add_scope.
End from_another_ab_group.
