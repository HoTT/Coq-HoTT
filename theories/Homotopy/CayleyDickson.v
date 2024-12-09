Require Import Types.Paths.
Require Import Classes.interfaces.abstract_algebra.
Require Import Cubical.DPath Cubical.PathSquare.
Require Import Pointed.Core Pointed.pSusp.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.Suspension.
Require Import Homotopy.Join.Core.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.

(** A Cayley-Dickson Spheroid is a pointed type X which is an H-space, with two operations called negation and conjugation, satisfying the seven following laws.
  --x=x   x**=x   1*=1    (-x)*=-x*   x(-y)=-(xy)   (xy)* = y* x*    x* x=1    *)
Class CayleyDicksonSpheroid (X : pType) := {
  cds_hspace : IsHSpace X;
  cds_negate : Negate X;
  cds_conjug : Conjugate X;
  cds_negate_inv : Involutive cds_negate;
  cds_conjug_inv : Involutive cds_conjug;
  cds_conjug_unit_pres : IsUnitPreserving cds_conjug;
  cds_conjug_left_inv : LeftInverse (.*.) cds_conjug mon_unit;
  cds_conjug_distr : DistrOpp (.*.) cds_conjug;
  cds_swapop : SwapOp (-) cds_conjug;
  cds_factorneg_r : FactorNegRight (-) (.*.);
}.
#[export] Existing Instances
  cds_hspace
  cds_negate
  cds_conjug
  cds_negate_inv
  cds_conjug_inv
  cds_conjug_unit_pres
  cds_conjug_left_inv
  cds_conjug_distr
  cds_swapop
  cds_factorneg_r.

Section CayleyDicksonSpheroid_Properties.

  Context {X : pType} `(CayleyDicksonSpheroid X).

  Local Instance isequiv_cds_conjug : IsEquiv cds_conjug
    := isequiv_adjointify cds_conjug cds_conjug cds_conjug_inv cds_conjug_inv.

  Global Instance cds_factorneg_l : FactorNegLeft (-) (.*.).
  Proof.
    intros x y.
    rapply (equiv_inj conj).
    lhs rapply distropp.
    rhs rapply swapop.
    rhs rapply (ap _ (distropp _ _)).
    rhs_V rapply factorneg_r.
    nrapply ap.
    apply swapop.
  Defined.

  Global Instance cds_conjug_right_inv : RightInverse (.*.) cds_conjug mon_unit.
  Proof.
    intro x.
    lhs_V rapply (ap (.* conj x) (involutive x)).
    rapply left_inverse.
  Defined.

End CayleyDicksonSpheroid_Properties.

Global Instance conjugate_susp (A : Type) `(Negate A)
  : Conjugate (Susp A)
  := Susp_rec North South (fun a => merid (-a)).

Global Instance negate_susp (A : Type) `(Negate A)
  : Negate (Susp A)
  := Susp_rec South North (fun a => (merid (-a))^).

Global Instance involutive_negate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (negate_susp A (-)).
Proof.
  snrapply Susp_ind_FFlr.
  1,2: reflexivity.
  intro x.
  lhs nrapply concat_p1.
  rhs nrapply concat_1p.
  lhs nrapply ap.
  1: nrapply Susp_rec_beta_merid.
  lhs nrapply (ap_V (negate_susp A negate) (merid (-x))).
  lhs nrapply ap.
  1: nrapply Susp_rec_beta_merid.
  lhs nrapply inv_V.
  nrapply ap.
  rapply (involutive x).
Defined.

Global Instance involutive_conjugate_susp {A} `(Negate A, !Involutive (-))
  : Involutive (conjugate_susp A (-)).
Proof.
  snrapply Susp_ind_FFlr.
  1,2: reflexivity.
  intro x.
  lhs nrapply concat_p1.
  rhs nrapply concat_1p.
  lhs nrapply ap.
  1: nrapply Susp_rec_beta_merid.
  lhs nrapply Susp_rec_beta_merid.
  nrapply ap.
  rapply (involutive x).
Defined.

Global Instance swapop_conjugate_susp {A} `(Negate A)
  : SwapOp negate (conjugate_susp A (-)).
Proof.
  snrapply Susp_ind_FFlFFr.
  1,2: reflexivity.
  intros x.
  lhs nrapply concat_p1.
  rhs nrapply concat_1p.
  rhs nrapply ap.
  2: nrapply Susp_rec_beta_merid.
  rhs nrapply Susp_rec_beta_merid.
  lhs nrapply ap.
  1: nrapply Susp_rec_beta_merid.
  lhs nrapply (ap_V _ (merid (-x))).
  apply ap.
  nrapply Susp_rec_beta_merid.
Defined.

Class CayleyDicksonImaginaroid (A : Type) := {
  cdi_negate : Negate A;
  cdi_negate_involutive : Involutive cdi_negate;
  cdi_susp_hspace : IsHSpace (psusp A);
  cdi_susp_factorneg_r : FactorNegRight (negate_susp A cdi_negate) hspace_op;
  cdi_susp_conjug_left_inv : LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit;
  cdi_susp_conjug_distr : DistrOpp hspace_op (conjugate_susp A cdi_negate);
}.
#[export] Existing Instances
  cdi_negate
  cdi_negate_involutive
  cdi_susp_hspace
  cdi_susp_factorneg_r
  cdi_susp_conjug_left_inv
  cdi_susp_conjug_distr.

Global Instance isunitpreserving_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : @IsUnitPreserving _ _ pt pt (conjugate_susp A cdi_negate).
Proof.
  reflexivity.
Defined.

(** Every suspension of a Cayley-Dickson imaginaroid gives a Cayley-Dickson spheroid. *)
Global Instance cds_susp_cdi {A} `(CayleyDicksonImaginaroid A)
  : CayleyDicksonSpheroid (psusp A) := {}.

Global Instance cdi_conjugate_susp_left_inverse {A} `(CayleyDicksonImaginaroid A)
  : LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  srapply cds_conjug_left_inv.
Defined.

Global Instance cdi_conjugate_susp_right_inverse {A} `(CayleyDicksonImaginaroid A)
  : RightInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  srapply cds_conjug_right_inv.
Defined.

Global Instance cdi_susp_left_identity {A} `(CayleyDicksonImaginaroid A)
  : LeftIdentity hspace_op mon_unit
  := _.

Global Instance cdi_susp_right_identity {A} `(CayleyDicksonImaginaroid A)
  : RightIdentity hspace_op mon_unit
  := _.

Global Instance cdi_negate_susp_factornegleft {A} `(CayleyDicksonImaginaroid A)
  : FactorNegLeft (negate_susp A cdi_negate) hspace_op.
Proof.
  srapply cds_factorneg_l.
Defined.

(** A Cayley-Dickson imaginaroid A whose multiplciation on the suspension is associative gives rise to a H-space structure on the join of the suspension of A with itself. *)
Section ImaginaroidHSpace.

  (* Let A be a Cayley-Dickson imaginaroid with associative H-space multiplication on Susp A *)
  Context {A} `(CayleyDicksonImaginaroid A)
    `(!Associative hspace_op).

  (** Declaring these as local instances so that they can be found *)
  Local Instance hspace_op' : SgOp (Susp A) := hspace_op.
  Local Instance hspace_unit' : MonUnit (Susp A) := hspace_mon_unit.

  (** First we make some observations with the context we have. *)
  Section Lemmata.

    Context (a b c d : Susp A).

    Local Definition f := (fun x => a * (c * -x)).
    Local Definition g := (fun y => c * (y * b)).

    Lemma lemma1 : f (- mon_unit) = a * c.
    Proof.
      unfold f; apply ap.
      exact (hspace_right_identity c).
    Defined.

    Lemma lemma2 : f (conj c * conj a * d * conj b) = (-d) * conj b.
    Proof.
      unfold f.
      rewrite 2 factorneg_r.
      rewrite 3 simple_associativity.
      rewrite <- distropp.
      rewrite (right_inverse (a * c)).
      rewrite (left_identity d).
      symmetry.
      apply factorneg_l.
    Defined.

    Lemma lemma3 : g mon_unit = c * b.
    Proof.
      unfold g; apply ap.
      apply left_identity.
    Defined.

    Lemma lemma4 : g (conj c * conj a * d * conj b) = conj a * d.
    Proof.
      unfold g.
      rewrite 2 simple_associativity.
      rewrite <- simple_associativity.
      rewrite left_inverse.
      rewrite right_identity.
      rewrite 2 simple_associativity.
      rewrite right_inverse.
      rewrite <- simple_associativity.
      apply left_identity.
    Defined.

  End Lemmata.

  Arguments f {_ _}.
  Arguments g {_ _}.

  (** Here is the multiplication map in algebraic form:
      (a,b) * (c,d) = (a * c - d * b*, a* * d + c * b)
      the following is the spherical form. *)
  Global Instance cd_op : SgOp (pjoin (psusp A) (psusp A)).
  Proof.
    snrapply Join_rec2.
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
      apply sq_path.
      rewrite <- (lemma1 a c).
      rewrite <- (lemma2 a b c d).
      rewrite <- (lemma3 b c).
      rewrite <- (lemma4 a b c d).
      refine (sq_GGGG _ _ _ _ _).
      2,4: apply ap.
      1,2,3,4: srapply (Join_rec_beta_jglue _ _ (fun a b => jglue (f a) (g b))).
      refine (sq_cGcG _ _ _).
      1,2: exact (ap_V _ (jglue _ _ )).
      refine (@sq_ap _ _ _ _ _ _ _ (jglue _ _) (jglue _ _)^
        (jglue _ _) (jglue _ _)^ _).
      change (PathSquare
        (jglue (- mon_unit) mon_unit)
        (jglue (conj c * conj a * d * conj b) (conj c * conj a * d * conj b))^
        (jglue (- mon_unit) (conj c * conj a * d * conj b))
        (jglue (conj c * conj a * d * conj b) mon_unit)^).
      generalize (conj c * conj a * d * conj b).
      clear a b c d.
      change (forall s : Susp A,
        Diamond (-mon_unit) s (mon_unit) s).
      srapply Susp_ind; hnf.
      1: by apply diamond_v_sq.
      1: by apply diamond_h_sq.
      intro a.
      apply diamond_twist.
  Defined.

  Global Instance cd_op_left_identity
    : LeftIdentity cd_op pt.
  Proof.
    snrapply Join_ind_Flr.
    1,2: exact (fun _ => ap _ (hspace_left_identity _)).
    intros a b.
    lhs nrapply whiskerR.
    1: nrapply (Join_rec_beta_jglue _ _ _ a b).
    symmetry.
    apply join_natsq.
  Defined.

  Global Instance cd_op_right_identity
    : RightIdentity cd_op pt.
  Proof.
    snrapply Join_ind_Flr.
    1: exact (fun _ => ap joinl (hspace_right_identity _)).
    1: exact (fun _ => ap joinr (hspace_left_identity _)).
    intros a b.
    lhs nrapply whiskerR.
    1: nrapply (Join_rec_beta_jglue _ _ _ a b).
    simpl; symmetry.
    apply join_natsq.
  Defined.

  Global Instance hspace_cdi_susp_assoc
    : IsHSpace (pjoin (psusp A) (psusp A))
    := {}.

End ImaginaroidHSpace.
