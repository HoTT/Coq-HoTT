From HoTT Require Import Basics.Overture.
Require Import
  HoTT.Classes.interfaces.abstract_algebra.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C f g.

(** Cancellation with one-sided inverse and unit laws does not require a group or set truncation. *)
Section inverse_cancellation.
  Local Open Scope path_scope.

  Definition sgop_inv_g_Vg {A : Type} `{op : SgOp A}
    {e : A} {i : A -> A}
    `{!Associative op, !LeftIdentity op e,
      !RightInverse op i e} (x y : A)
    : x * (i x * y) = y
    := simple_associativity _ _ _
        @ ap (.* y) (right_inverse x)
        @ left_identity y.

  Definition sgop_inv_V_gg {A : Type} `{op : SgOp A}
    {e : A} {i : A -> A}
    `{!Associative op, !LeftIdentity op e,
      !LeftInverse op i e} (x y : A)
    : i x * (x * y) = y
    := simple_associativity _ _ _
        @ ap (.* y) (left_inverse x)
        @ left_identity y.

  Definition sgop_inv_gV_g {A : Type} `{op : SgOp A}
    {e : A} {i : A -> A}
    `{!Associative op, !RightIdentity op e,
      !LeftInverse op i e} (x y : A)
    : (x * i y) * y = x
    := (simple_associativity _ _ _)^
        @ ap (x *.) (left_inverse y)
        @ right_identity x.

  Definition sgop_inv_gg_V {A : Type} `{op : SgOp A}
    {e : A} {i : A -> A}
    `{!Associative op, !RightIdentity op e,
      !RightInverse op i e} (x y : A)
    : (x * y) * i y = x
    := (simple_associativity _ _ _)^
        @ ap (x *.) (right_inverse y)
        @ right_identity x.

End inverse_cancellation.

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
  exact (sgop_inv_gV_g (op:=op) (e:=unit) (i:=inv)
           (RightIdentity0:=monoid_right_id A) (LeftInverse0:=inverse_l A) x y).
Defined.

(** Cancelling a right inverse [op y (inv y)]. *)
Lemma right_inverse_cancel {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsGroup A op unit inv} (x y : A)
  : op (op x y) (inv y) = x.
Proof.
  exact (sgop_inv_gg_V (op:=op) (e:=unit) (i:=inv)
           (RightIdentity0:=monoid_right_id A) (RightInverse0:=inverse_r A) x y).
Defined.

Lemma inverse_telescope {A} (op : A -> A -> A) {inv : A -> A} {unit : A}
  `{!@IsGroup A op unit inv} (x y z : A)
  : op (op x (inv y)) (op y (inv z)) = op x (inv z).
Proof.
  lhs rapply simple_associativity.
  exact (ap (fun w => op w (inv z)) (left_inverse_cancel op x y)).
Qed.

(** The properties in this section can also be proved without assuming that [G] is set-truncated, but currently typeclass inference can fail to find these results for rings if proved without the [IsGroup] hypothesis. *)
Section group_props.
  Context `{IsGroup G}.

  (** Group inverses are involutive *)
  #[export] Instance inverse_involutive : Involutive (^).
  Proof.
    intros x.
    rhs_V rapply left_identity.
    lhs_V rapply (sgop_inv_gV_g _ x).
    exact (ap (.* x) (left_inverse _)).
  Qed.

  #[export] Instance isinj_group_inverse : IsInjective (^).
  Proof.
    intros x y E.
    refine ((involutive x)^ @ _ @ involutive y).
    apply ap, E.
  Qed.

  Lemma inverse_mon_unit : mon_unit^ = mon_unit.
  Proof.
    rhs_V rapply (left_inverse mon_unit).
    apply symmetry, right_identity.
  Qed.

  #[export] Instance group_cancelL : forall z : G, LeftCancellation (.*.) z.
  Proof.
    intros z x y E.
    rhs_V rapply (sgop_inv_V_gg z).
    lhs_V rapply (sgop_inv_V_gg z).
    exact (ap _ E).
  Defined.

  #[export] Instance group_cancelR: forall z : G, RightCancellation (.*.) z.
  Proof.
    intros z x y E.
    rhs_V rapply (sgop_inv_gg_V _ z).
    lhs_V rapply (sgop_inv_gg_V _ z).
    exact (ap (.* z^) E).
  Qed.

  Lemma inverse_sg_op x y : (x * y)^ = y^ * x^.
  Proof.
    apply (group_cancelL (x * y)).
    lhs rapply right_inverse.
    symmetry.
    lhs rapply simple_associativity.
    lhs rapply (ap (.* x^) (sgop_inv_gg_V _ _)).
    apply right_inverse.
  Defined.

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
