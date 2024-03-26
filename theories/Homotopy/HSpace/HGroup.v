Require Import Basics Types.
Require Import Pointed.Core HSpace.Core Truncations.Core abstract_algebra.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** A H-monoid is a H-space with an associative binary operation. *)
Class IsHMonoid (X : pType) := {
  ishspace_ishmonoid :: IsHSpace X;
  assoc_ishmonoid :: Associative (.*.);
}.

(** A H-commutative monoid is a H-space with an associative and commutative binary operation. *)
Class IsHCommutativeMonoid (X : pType) := {
  ishmonoid_ishcommutativemonoid :: IsHMonoid X;
  comm_ishcomutativemonoid :: Commutative (.*.);
}.
  
(** A H-group is a H-space with an associative binary operation an inversion. *)
Class IsHGroup (X : pType) := {
  ishmonoid_ishgroup :: IsHMonoid X;
  negate_ishgroup :: Negate X;
  left_inverse_ishgroup :: LeftInverse (.*.) (-) pt;
  right_inverse_ishgroup :: RightInverse (.*.) (-) pt;
}.

(** A H-abelian group is a H-space with an associative and commutative binary operation and invertible left and right multiplication. *)
Class IsHAbGroup (X : pType) := {
  ishgroup_ishabeliangroup :: IsHGroup X;
  comm_ishabeliangroup :: Commutative (.*.);
}.

(** The 0-truncation of a space with an operation has a truncated version of that operation. *)
Local Instance sgop_tr X `{SgOp X} : SgOp (Tr 0 X).
Proof.
  intros x y.
  strip_truncations.
  apply tr.
  exact (x * y).
Defined.  

(** The 0-truncation of a space with unit has a truncated unit. *)
Local Instance monoid_unit_tr X `{MonUnit X} : MonUnit (Tr 0 X).
Proof.
  apply tr.
  exact mon_unit.
Defined.

(** The 0-truncation of a H-monoid is a monoid. *)
Global Instance ismonoid_ishmonoid_tr X `{IsHMonoid X} : IsMonoid (Tr 0 X).
Proof.
  repeat split.
  1: exact _.
  - intros x y z.
    strip_truncations.
    apply (ap tr).
    apply assoc_ishmonoid.
  - intros x.
    strip_truncations.
    apply (ap tr).
    apply left_identity.
  - intros x.
    strip_truncations.
    apply (ap tr).
    apply right_identity.
Defined.

(** The 0-truncation of a H-commutative monoid is a commutative monoid. *)
Local Instance iscommutativemonoid_ishcommutativemonoid_tr X `{IsHCommutativeMonoid X}
  : IsCommutativeMonoid (Tr 0 X).
Proof.
  split.
  1: exact _.
  intros x y.
  strip_truncations.
  apply (ap tr).
  apply (comm_ishcomutativemonoid x y).
Defined.

(** The 0-truncation of a space with invertible left and right multiplication has a negation. *)
Local Instance neg_tr X `{Negate X} : Negate (Tr 0 X).
Proof.
  intros x.
  strip_truncations.
  apply tr.
  exact (- x).
Defined.

(** The 0-truncation of a H-group is a group. *)
Global Instance isgroup_ishgroup_tr X `{IsHGroup X} : IsGroup (Tr 0 X).
Proof.
  split.
  1: exact _.
  - intros x.
    strip_truncations.
    apply (ap tr).
    rapply left_inverse.
  - intros x.
    strip_truncations.
    apply (ap tr).
    rapply right_inverse.
Defined.

(** The 0-truncation of a H-abelian group is an abelian group. *)
Global Instance isabgroup_ishabgroup_tr X `{IsHAbGroup X}
  : IsAbGroup (Tr 0 X).
Proof.
  split.
  1: exact _.
  intros x y.
  strip_truncations.
  apply (ap tr).
  apply (comm_ishabeliangroup x y).
Defined.
