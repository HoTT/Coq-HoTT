Require Import Basics.
Require Import Types.
Require Import Cubical.
Require Import Pointed.
Require Import Homotopy.HSpace.
Require Import Homotopy.Suspension.
Require Import Homotopy.Join.

Local Open Scope mc_mult_scope.

(** A Cayley-Dickson Spheroid is a pointed type X which is an H-space, with two operations called negation and conjugation, satisfying the seven following laws.
  --x=x   x**=x   1*=1    (-x)*=-x*   x(-y)=-(xy)   (xy)* = y* x*    x* x=1    *)
Class CayleyDicksonSpheroid (X : pType) := {
  cds_hspace :> IsHSpace X;
  cds_negate :> Negate X;
  cds_conjug :> Conjugate X;
  cds_negate_inv :> Involutive cds_negate;
  cds_conjug_inv :> Involutive cds_conjug;
  cds_conjug_unit_pres :> IsUnitPreserving cds_conjug;
  cds_conjug_left_inv :> LeftInverse (.*.) cds_conjug mon_unit;
  cds_conjug_distr :> DistrOpp (.*.) cds_conjug;
  cds_swapop :> SwapOp (-) cds_conjug;
  cds_factorneg_r :> FactorNegRight (-) (.*.);
}.

Section CayleyDicksonSpherioid_Properties.

  Context {X : pType} `(CayleyDicksonSpheroid X).

  Global Instance cds_factorneg_l : FactorNegLeft (-) (.*.).
  Proof.
    intros x y.
    transitivity (conj (conj (-x * y))).
    1: symmetry; apply involutive.
    rewrite distropp.
    rewrite swapop.
    rewrite factorneg_r.
    rewrite swapop.
    rewrite <- distropp.
    rewrite involutive.
    reflexivity.
  Defined.

  Global Instance cds_conjug_right_inv
    : RightInverse (.*.) cds_conjug mon_unit.
  Proof.
    intro x.
    set (p := cds_conjug x).
    rewrite <- (involutive x).
    apply left_inverse.
  Defined.

End CayleyDicksonSpherioid_Properties.

Global Instance conjugate_susp (A : Type) `(Negate A)
  : Conjugate (Susp A).
Proof.
  serapply Susp_rec.
  + exact North.
  + exact South.
  + intro a.
    exact (merid a).
Defined.

Global Instance negate_susp (A : Type) `(Negate A)
  : Negate (Susp A).
Proof.
  serapply Susp_rec.
  + exact South.
  + exact North.
  + intro a.
    exact (merid (-a))^.
Defined.

Class CayleyDicksonImaginaroid (A : Type) := {
  cdi_negate :> Negate A;
  cdi_negate_involutive :> Involutive cdi_negate;
  cdi_susp_hspace :> IsHSpace (Build_pType (Susp A) _);
  cdi_susp_factorneg_r :> FactorNegRight (negate_susp A cdi_negate) hspace_op;
  cdi_susp_conjug_left_inv
    :> LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit;
  cdi_susp_conjug_distr :> DistrOpp hspace_op (conjugate_susp A cdi_negate);
}.

Global Instance involutive_negate_susp {A} `(CayleyDicksonImaginaroid A)
  : Involutive (negate_susp A cdi_negate).
Proof.
  serapply Susp_ind_dp; try reflexivity.
  intro x.
  apply dp_paths_FFlr.
  rewrite concat_p1.
  rewrite Susp_rec_beta_merid.
  rewrite ap_V.
  rewrite Susp_rec_beta_merid.
  rewrite inv_V.
  rewrite (involutive x).
  apply concat_Vp.
Defined.

Global Instance involutive_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : Involutive (conjugate_susp A cdi_negate).
Proof.
  serapply Susp_ind_dp; try reflexivity.
  intro x.
  apply dp_paths_FFlr.
  rewrite concat_p1.
  rewrite 2 Susp_rec_beta_merid.
  apply concat_Vp.
Defined.

Global Instance isunitpreserving_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : @IsUnitPreserving _ _ (point _) (point _) (conjugate_susp A cdi_negate).
Proof.
  reflexivity.
Defined.

Global Instance swapop_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : SwapOp negate (conjugate_susp A cdi_negate).
Proof.
  serapply Susp_ind_dp; try reflexivity.
  intro x.
  apply dp_paths_FlFr.
  rewrite concat_p1.
  rewrite ap_compose.
  rewrite (ap_compose negate).
  rewrite Susp_rec_beta_merid.
  rewrite ap_V.
  rewrite inv_V.
  rewrite 3 Susp_rec_beta_merid.
  apply concat_pV.
Defined.

(** Every suspension of a Cayley-Dickson imaginaroid gives a Cayley-Dickson spherioid. *)
Global Instance cds_susp_cdi {A} `(CayleyDicksonImaginaroid A)
  : CayleyDicksonSpheroid (Build_pType (Susp A) _) := {}.

Global Instance cdi_conjugate_susp_left_inverse {A} `(CayleyDicksonImaginaroid A)
  : LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  serapply cds_conjug_left_inv.
Defined.

Global Instance cdi_conjugate_susp_right_inverse {A} `(CayleyDicksonImaginaroid A)
  : RightInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  serapply cds_conjug_right_inv.
Defined.

Global Instance cdi_susp_left_identity {A} `(CayleyDicksonImaginaroid A)
  : LeftIdentity hspace_op mon_unit.
Proof.
  exact _.
Defined.

Global Instance cdi_susp_right_identity {A} `(CayleyDicksonImaginaroid A)
  : RightIdentity hspace_op mon_unit.
Proof.
  exact _.
Defined.

Global Instance cdi_negate_susp_factornegleft {A} `(CayleyDicksonImaginaroid A)
  : FactorNegLeft (negate_susp A cdi_negate) hspace_op.
Proof.
  serapply cds_factorneg_l.
Defined.

(** A Cayley-Dickson imaginaroid A whose multiplciation on the suspension is associative gives rise to a H-space structure on the join of the suspension of A with itself. *)
Section ImaginaroidHSpace.

  (* Let A be a Cayley-Dickson imaginaroid with associative H-space multiplication on Susp A *)
  Context `{Funext} {A} `(CayleyDicksonImaginaroid A)
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
  Global Instance cd_op
    : SgOp (Build_pType (Join (Susp A) (Susp A)) (joinl (point _))).
  Proof.
    serapply Join_rec; hnf.
    { intro a.
      serapply Join_rec; hnf.
      - intro c.
        exact (joinl (hspace_op a c)).
      - intro d.
        exact (joinr (hspace_op (conj a) d)).
      - intros x y.
        apply jglue. }
    { intro b.
      serapply Join_rec; hnf.
      - intro c.
        exact (joinr (hspace_op c b)).
      - intro d.
        exact (joinl (hspace_op (-d) (conj b))).
      - intros x y.
        symmetry.
        apply jglue. }
    intros a b.
    apply path_forall.
    serapply Join_ind.
    1: intro; apply jglue.
    1: intro; cbn; symmetry; apply jglue.
    intros c d.
    serapply sq_dp^-1.
    refine (sq_ccGG _^ _^ _).
    1,2: apply Join_rec_beta_jglue.
    change (PathSquare (jglue (a * c) (c * b)) (jglue ((- d) * conj b) (conj a * d))^
      (jglue (a * c) (conj a * d)) (jglue ((- d) * conj b) (c * b))^).
    rewrite <- (lemma1 a c), <- (lemma2 a b c d),
       <- (lemma3 b c), <- (lemma4 a b c d).
    refine (sq_GGGG _ _ _ _ _).
    2,4: apply ap.
    1,2,3,4: serapply (Join_rec_beta_jglue _ _ (fun a b => jglue (f a) (g b))).
    refine (sq_cGcG _ _ _).
    1,2: exact (ap_V _ (jglue _ _ )).
    refine (@sq_ap _ _ _ _ _ _ _ (jglue _ _) (jglue _ _)^
      (jglue _ _) (jglue _ _)^ _).
    generalize (conj c * conj a * d * conj b).
    clear a b c d.
    change (forall s : Susp A,
      Diamond (-mon_unit) s (mon_unit) s).
    serapply Susp_ind_dp; hnf.
    1: by apply diamond_v.
    1: by apply diamond_h.
    intro a.
    apply diamond_twist.
  Defined.

  Global Instance cd_op_left_identity
    : LeftIdentity cd_op (point _).
  Proof.
    serapply Join_ind; simpl.
    { intro a; apply ap.
      serapply hspace_left_identity. }
    { intro b; apply ap.
      serapply hspace_left_identity. }
    intros a b.
    apply sq_dp^-1.
    rewrite ap_idmap, Join_rec_beta_jglue.
    apply join_natsq_v.
  Defined.

  Global Instance cd_op_right_identity
    : RightIdentity cd_op (point _).
  Proof.
    serapply Join_ind; simpl.
    { intro a; apply ap.
      serapply hspace_right_identity. }
    { intro b; apply ap.
      serapply hspace_left_identity. }
    intros a b.
    apply sq_dp^-1.
    rewrite ap_idmap.
    rewrite (ap_compose _ (fun f => f _)).
    rewrite Join_rec_beta_jglue.
    rewrite ap_apply_l.
    rewrite eisretr.
    apply join_natsq_v.
  Defined.

  Global Instance hspace_cdi_susp_assoc
    : IsHSpace (Build_pType (Join (Susp A) (Susp A)) (joinl (point _)))
    := {}.

End ImaginaroidHSpace.
