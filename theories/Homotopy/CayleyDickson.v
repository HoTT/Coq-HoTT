From HoTT Require Import Basics.
Require Import Classes.interfaces.abstract_algebra Classes.theory.groups.
Require Import Pointed.Core Pointed.pSusp.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.Suspension.
Require Import Homotopy.Join.Core Homotopy.Join.JoinSusp.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The Cayley-Dickson Construction *)

(** The Cayley-Dickson construction in homotopy type theory due to Buchholtz and Rijke https://arxiv.org/abs/1610.01134 is a method to construct an H-space structure on the join of two suspensions of a type [A]. As a special case, this gives a way to construct an H-space structure on [S^3] leading to the quaternionic Hopf fibration.

The construction works by replicating the classical Cayley-Dickson construction on convolution algebras ([*]-algebras), which can produce the complex numbers, quaternions, octonions, etc. starting with the real numbers. We cannot replicate this directly in HoTT since such algebras have a contractible underlying vector space, therefore the construction here attempts to axiomatize the properties of the units of those algebras instead.

This is done by postulating a structure called a "Cayley-Dickson imaginaroid" on a type [A] and showing that [Join (Susp A) (Susp A)] is an H-space. An open problem is to show that this space itself is also an imaginaroid given further, yet unspecified, coherences on [A]. *)

(** ** Cayley-Dickson spheroids *)

(** A Cayley-Dickson Spheroid is a pointed type X which is an H-space, with two operations called negation and conjugation, satisfying the following seven laws:
  1. [--x = x]
  2. [x** = x]
  3. [1* = 1]
  4. [(-x)* = -x*]
  5. [x(-y) = -(xy)]
  6. [(xy)* = y* x*]
  7. [x* x = 1]
Note that the above laws are written in pseudocode since we cannot define multiplication by juxtaposition in Coq, and * is used to denote conjugation. *)
Class CayleyDicksonSpheroid (X : pType) := {
  cds_hspace :: IsHSpace X;
  cds_negate :: Negate X;
  cds_conjug :: Conjugate X;
  cds_negate_inv :: Involutive cds_negate;
  cds_conjug_inv :: Involutive cds_conjug;
  cds_conjug_unit_pres :: IsUnitPreserving cds_conjug;
  cds_conjug_left_inv :: LeftInverse (.*.) cds_conjug mon_unit;
  cds_conjug_distr :: DistrOpp (.*.) cds_conjug;
  cds_swapop :: SwapOp (-) cds_conjug;
  cds_factorneg_r :: FactorNegRight (-) (.*.)
}.

Section CayleyDicksonSpheroid_Properties.

  Context {X : pType} `(CayleyDicksonSpheroid X).

  Local Instance isequiv_cds_conjug : IsEquiv cds_conjug
    := isequiv_involution cds_conjug cds_conjug_inv.

  #[export] Instance cds_factorneg_l : FactorNegLeft (-) (.*.).
  Proof.
    intros x y.
    rapply (equiv_inj conj).
    lhs rapply distropp.
    rhs rapply swapop.
    rhs rapply (ap _ (distropp _ _)).
    rhs_V rapply factorneg_r.
    napply ap.
    apply swapop.
  Defined.

  #[export] Instance cds_conjug_right_inv : RightInverse (.*.) cds_conjug mon_unit.
  Proof.
    intro x.
    lhs_V exact (ap (.* conj x) (involutive x)).
    rapply left_inverse.
  Defined.

End CayleyDicksonSpheroid_Properties.

(** ** Negation and conjugation on suspensions *)

Instance conjugate_susp (A : Type) `(Negate A) : Conjugate (Susp A)
  := functor_susp (-).

Instance negate_susp (A : Type) `(Negate A) : Negate (Susp A)
  := susp_neg _ o conjugate_susp A (-).

(** [conjugate_susp A] and [negate_susp A] commute. *)
Instance swapop_conjugate_susp {A} `(Negate A)
  : SwapOp (negate_susp A (-)) (conjugate_susp A (-)).
Proof.
  intros x.
  symmetry.
  napply susp_neg_natural.
Defined.

(** [conjugate_susp A] is involutive, since any functor applied to an involution gives an involution. *)
Instance involutive_conjugate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (conjugate_susp A (-)).
Proof.
  intros x.
  lhs_V napply functor_susp_compose.
  rhs_V napply functor_susp_idmap.
  napply functor2_susp.
  exact involutive.
Defined.

(** [conjugate_susp A] is involutive as any composite of commuting involutions is an involution. *)
Instance involutive_negate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (negate_susp A (-)).
Proof.
  intros x.
  unfold negate_susp.
  lhs napply ap.
  1: napply swapop_conjugate_susp.
  lhs rapply susp_neg_inv.
  rapply involutive.
Defined.

(** ** Cayley-Dickson imaginaroids *)

Class CayleyDicksonImaginaroid (A : Type) := {
  cdi_negate :: Negate A;
  cdi_negate_involutive :: Involutive cdi_negate;
  cdi_susp_hspace :: IsHSpace (psusp A);
  cdi_susp_factorneg_r :: FactorNegRight (negate_susp A cdi_negate) hspace_op;
  cdi_susp_conjug_left_inv :: LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit;
  cdi_susp_conjug_distr :: DistrOpp hspace_op (conjugate_susp A cdi_negate);
}.

Instance isunitpreserving_conjugate_susp {A} `(Negate A)
  : @IsUnitPreserving _ _ pt pt (conjugate_susp A _)
  := idpath.

(** Every suspension of a Cayley-Dickson imaginaroid gives a Cayley-Dickson spheroid. *)
Instance cds_susp_cdi {A} `(CayleyDicksonImaginaroid A)
  : CayleyDicksonSpheroid (psusp A) := {}.

Instance cdi_conjugate_susp_right_inverse {A} `(CayleyDicksonImaginaroid A)
  : RightInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  stapply cds_conjug_right_inv.
Defined.

Instance cdi_susp_left_identity {A} `(CayleyDicksonImaginaroid A)
  : LeftIdentity hspace_op mon_unit
  := _.

Instance cdi_susp_right_identity {A} `(CayleyDicksonImaginaroid A)
  : RightIdentity hspace_op mon_unit
  := _.

Instance cdi_negate_susp_factornegleft {A} `(CayleyDicksonImaginaroid A)
  : FactorNegLeft (negate_susp A cdi_negate) hspace_op.
Proof.
  stapply cds_factorneg_l.
Defined.

(** A Cayley-Dickson imaginaroid [A] whose multiplication on the suspension is associative gives rise to an H-space structure on the join of the suspension of [A] with itself. *)
Section ImaginaroidHSpace.

  (** Let [A] be a Cayley-Dickson imaginaroid with associative H-space multiplication on [Susp A]. *)
  Context {A} `(CayleyDicksonImaginaroid A) `(!Associative hspace_op).

  (** Declaring these as local instances so that they can be found *)
  Local Instance hspace_op' : SgOp (Susp A) := hspace_op.
  Local Instance hspace_unit' : MonUnit (Susp A) := hspace_mon_unit.

  Local Definition cd_diamond_map_l (a c : Susp A)
    := fun x => a * (c * -x).
  Local Definition cd_diamond_map_r (b c : Susp A)
    := fun y => c * (y * b).

  Section ScalarBoundary.

    Context (a b c d : Susp A).

    Lemma cd_diamond_map_l_neg_unit
      : cd_diamond_map_l a c (- mon_unit) = a * c.
    Proof.
      unfold cd_diamond_map_l; apply ap.
      exact (hspace_right_identity c).
    Defined.

    Lemma cd_diamond_map_l_parameter
      : cd_diamond_map_l a c ((conj c * (conj a * d)) * conj b)
        = (-d) * conj b.
    Proof.
      unfold cd_diamond_map_l.
      lhs tapply (ap (a *.) (factorneg_r _ _)).
      lhs tapply factorneg_r.
      rhs tapply factorneg_l.
      napply ap.
      lhs tapply (ap (a *.) (simple_associativity (f:=(.*.)) _ _ _)).
      lhs tapply (simple_associativity (f:=(.*.))).
      napply (ap (.* conj b)).
      lhs tapply (ap (a *.) (sgop_inv_cancel_l c _)).
      rapply sgop_inv_cancel_l.
    Defined.

    Lemma cd_diamond_map_r_unit
      : cd_diamond_map_r b c mon_unit = c * b.
    Proof.
      unfold cd_diamond_map_r; apply ap.
      apply left_identity.
    Defined.

    Lemma cd_diamond_map_r_parameter
      : cd_diamond_map_r b c ((conj c * (conj a * d)) * conj b)
        = conj a * d.
    Proof.
      unfold cd_diamond_map_r.
      lhs tapply (ap (c *.) (sgop_inv_cancel_r _ b)).
      tapply sgop_inv_cancel_l.
    Defined.

  End ScalarBoundary.

  (** Here is the multiplication map in algebraic form: [(a,b) * (c,d) = (a * c - d * b*, a* * d + c * b)].  The following is the spherical form. *)
  #[export] Instance cd_op : SgOp (pjoin (psusp A) (psusp A)).
  Proof.
    snapply Join_rec2.
    - exact (fun a b => joinl (a * b)).
    - exact (fun a b => joinr (conj a * b)).
    - exact (fun a b => joinr (b * a)).
    - exact (fun a b => joinl ((- b) * conj a)).
    - intros; apply jglue.
    - intros; symmetry; apply jglue.
    - intros; apply jglue.
    - intros; symmetry; apply jglue.
    - intros a b c d; cbn beta.
      symmetry.
      change (diamond (a * c) ((-d) * conj b) (c * b) (conj a * d)).
      rewrite <- (cd_diamond_map_l_neg_unit a c).
      (** Rewrite this corner first since the other also contains [conj a * d]. *)
      rewrite <- (cd_diamond_map_r_parameter a b c d).
      rewrite <- (cd_diamond_map_l_parameter a b c d).
      rewrite <- (cd_diamond_map_r_unit b c).
      napply (functor_diamond (cd_diamond_map_l a c) (cd_diamond_map_r b c)).
      apply diamond_susp.
  Defined.

  #[export] Instance cd_op_left_identity
    : LeftIdentity cd_op pt.
  Proof.
    intro z.
    lhs napply (functor2_join hspace_left_identity hspace_left_identity).
    napply functor_join_idmap.
  Defined.

  #[export] Instance cd_op_right_identity
    : RightIdentity cd_op pt.
  Proof.
    intro z.
    lhs napply (functor2_join hspace_right_identity hspace_left_identity).
    napply functor_join_idmap.
  Defined.

  #[export] Instance hspace_cdi_susp_assoc
    : IsHSpace (pjoin (psusp A) (psusp A))
    := {}.

End ImaginaroidHSpace.
