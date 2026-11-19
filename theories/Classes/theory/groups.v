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

(** ** Equations with minimal algebraic laws *)

Lemma swap_middle {A} `{op : SgOp A}
  `{!Associative op, !Commutative op} (a b c d : A)
  : (a * b) * (c * d) = (a * c) * (b * d).
Proof.
  lhs_V rapply simple_associativity.
  rhs_V rapply simple_associativity.
  apply (ap (a *.)).
  lhs rapply simple_associativity.
  rhs rapply simple_associativity.
  exact (ap (.* d) (commutativity b c)).
Qed.

Lemma inverse_telescope {A} `{op : SgOp A} {e : A} {i : A -> A}
  `{!Associative op, !LeftInverse op i e, !RightIdentity op e}
  (x y z : A)
  : (x * i y) * (y * i z) = x * i z.
Proof.
  lhs rapply simple_associativity.
  exact (ap (fun w => w * i z) (sgop_inv_gV_g x y)).
Qed.

Section group_props.
  Context {G : Type} `{op : SgOp G} `{unit : MonUnit G}
    `{i : Inverse G} `{!Associative (.*.), !LeftIdentity (.*.) mon_unit,
      !RightIdentity (.*.) mon_unit, !LeftInverse (.*.) (^) mon_unit,
      !RightInverse (.*.) (^) mon_unit}.

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

  Context {G : Type} `{op : SgOp G} `{unit : MonUnit G}
    `{i : Inverse G} `{!Associative (+), !Commutative (+),
      !LeftIdentity (+) 0, !RightIdentity (+) 0,
      !LeftInverse (+) (-) 0, !RightInverse (+) (-) 0}.

  Lemma negate_sg_op_distr x y : -(x + y) = -x + -y.
  Proof.
    exact (inverse_sg_op x y @ commutativity _ _).
  Qed.

  Lemma common_left_cancel (x y z : G) : (z + x) - (z + y) = x - y.
  Proof.
    lhs rapply (ap (sg_op (z + x)) (negate_sg_op_distr z y)).
    lhs rapply swap_middle.
    lhs exact (ap (fun w => w + (x - y)) (right_inverse z)).
    rapply left_identity.
  Qed.

  Local Close Scope mc_add_scope.
End abgroup_props.

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
