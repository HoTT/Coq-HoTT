From HoTT Require Import Basics.
Require Import Types.Paths.
Require Import Classes.interfaces.abstract_algebra.
Require Import Pointed.Core Pointed.pSusp.
Require Import Homotopy.HSpace.Core.
Require Import Homotopy.Suspension.
Require Import Homotopy.Join.Core.

Local Open Scope pointed_scope.
Local Open Scope mc_mult_scope.
Local Open Scope path_scope.

(** The Cayley-Dickson Construction *)

(** The Cayley-Dickson construction in homotopy type theory due to Buchholtz and Rijke https://arxiv.org/abs/1610.01134 is a method to construct an H-space structure on the join of two suspensions of a type [A]. As a special case, this gives a way to construct an H-space structure on [S^3] leading to the quaternionic Hopf fibration.

The construction works by replicating the classical Cayley-Dickson construction on convolution algebras ([*]-algebras), which can produce the complex numbers, quaternions, octonions, etc. starting with the real numbers. We cannot replicate this directly in HoTT since such algebras have a contractible underlying vector space, therefore the construction here attempts to axiomatize the properties of the units of those algebras instead.

This is done by postulating a structure called a "Cayley-Dickson imaginaroid" on a type [A] and showing that [Join (Susp A) (Susp A)] is an H-space. Here we separate the algebra from the geometry: an associative spheroid [X] with a chosen diamond gives an H-space on [Join X X], and suspensions supply the canonical diamond. We also prove the doubled involution and inverse laws, without additional coherences of the diamond. Anti-multiplicativity of doubled conjugation and associativity of the doubled multiplication are not established here. Recovering an imaginaroid on [Join A (Susp A)] remains an open problem requiring further coherences. *)

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
    := isequiv_adjointify cds_conjug cds_conjug cds_conjug_inv cds_conjug_inv.

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

(** ** Chosen diamonds *)

(** The geometric input to doubling a spheroid is a chosen filler, not merely the assertion that a filler exists. We express it as an equality of zigzags, so the construction only needs path algebra. No multiplication or associativity is needed to state this data. Additional laws for the doubled multiplication can then be formulated as coherences of this choice. *)
Class CayleyDicksonDiamond (X : pType) (neg : X -> X)
  := cd_diamond : forall t : X,
    zigzag (neg pt) t pt = zigzag (neg pt) t t.

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

(** Every suspension supplies a canonical diamond. Only the value of suspension negation at the north pole is used; no laws of the negation on [A], or multiplication on [Susp A], are needed. *)
Instance cd_diamond_susp {A : Type} `{Negate A}
  : CayleyDicksonDiamond (psusp A) (-)
  := Susp_ind (fun t => zigzag South t North = zigzag South t t)
       (diamond_v South North 1) (diamond_h North South 1)
       (fun a => diamond_twist (merid a)).

(** ** Cayley-Dickson imaginaroids *)

Class CayleyDicksonImaginaroid (A : Type) := {
  cdi_negate :: Negate A;
  cdi_negate_involutive :: Involutive cdi_negate;
  cdi_susp_hspace :: IsHSpace (psusp A);
  cdi_susp_factorneg_r :: FactorNegRight (negate_susp A cdi_negate) hspace_op;
  cdi_susp_conjug_left_inv :: LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit;
  cdi_susp_conjug_distr :: DistrOpp hspace_op (conjugate_susp A cdi_negate);
}.

Instance isunitpreserving_conjugate_susp {A} `(CayleyDicksonImaginaroid A)
  : @IsUnitPreserving _ _ pt pt (conjugate_susp A cdi_negate)
  := idpath.

(** Every suspension of a Cayley-Dickson imaginaroid gives a Cayley-Dickson spheroid. *)
Instance cds_susp_cdi {A} `(CayleyDicksonImaginaroid A)
  : CayleyDicksonSpheroid (psusp A) := {}.

Instance cdi_conjugate_susp_left_inverse {A} `(CayleyDicksonImaginaroid A)
  : LeftInverse hspace_op (conjugate_susp A cdi_negate) mon_unit.
Proof.
  exact cds_conjug_left_inv.
Defined.

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

(** ** Negation and conjugation on the double *)

Instance cd_negate {X : Type} `{Negate X} : Negate (Join X X)
  := functor_join (-) (-).

Instance cd_conjugate {X : Type} `{Negate X, Conjugate X}
  : Conjugate (Join X X)
  := functor_join conj (-).

Instance involutive_cd_negate {X : Type}
  `{Negate X, !Involutive (-)} : Involutive cd_negate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_idmap.
  napply functor2_join; exact involutive.
Defined.

Instance involutive_cd_conjugate {X : Type}
  `{Negate X, Conjugate X, !Involutive (-), !Involutive conj}
  : Involutive cd_conjugate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_idmap.
  napply functor2_join; exact involutive.
Defined.

Instance swapop_cd {X : Type} `{Negate X, Conjugate X, !SwapOp (-) conj}
  : SwapOp cd_negate cd_conjugate.
Proof.
  intro x.
  lhs_V napply functor_join_compose.
  rhs_V napply functor_join_compose.
  napply functor2_join.
  1: exact swapop.
  reflexivity.
Defined.

Instance isunitpreserving_cd_conjugate {X : pType}
  `{Negate X, Conjugate X, !@IsUnitPreserving X X pt pt conj}
  : @IsUnitPreserving (pjoin X X) (pjoin X X) pt pt cd_conjugate
  := ap joinl preserves_mon_unit.

(** ** Multiplication on the double *)

(** An associative Cayley-Dickson spheroid with a chosen diamond gives an H-space structure on its self-join. For an imaginaroid, [cd_diamond_susp] supplies the diamond automatically. *)
Section SpheroidHSpace.

  Context {X : pType} `{CayleyDicksonSpheroid X}
    `{!Associative hspace_op} `{!CayleyDicksonDiamond X (-)}.

  (** These are the four scalar boundary identifications for the image of the chosen diamond under the join map induced by [f] and [g]. *)
  Section Lemmata.

    Context (a b c d : X).

    Local Definition f := (fun x => a * (c * -x)).
    Local Definition g := (fun y => c * (y * b)).
    Local Notation assoc := (simple_associativity (f:=hspace_op)).

    Lemma lemma1 : f (- mon_unit) = a * c.
    Proof.
      exact (ap (fun x => a * (c * x)) (cds_negate_inv mon_unit)
        @ ap (a *.) (hspace_right_identity c)).
    Defined.

    Lemma lemma2 : f (conj c * conj a * d * conj b) = (-d) * conj b.
    Proof.
      (** Move the sign out, then cancel [a * c] against its conjugate. *)
      refine (ap (a *.) (factorneg_r c _) @ factorneg_r a _
        @ ap (-) _ @ (factorneg_l d (conj b))^).
      refine (assoc a c _ @ assoc (a * c) _ (conj b)
        @ ap (.* conj b) _).
      exact (assoc (a * c) _ d
        @ ap (.* d) (ap ((a * c) *.) (distropp a c)^
          @ right_inverse (a * c))
        @ left_identity d).
    Defined.

    Lemma lemma3 : g mon_unit = c * b.
    Proof.
      exact (ap (c *.) (left_identity b)).
    Defined.

    Lemma lemma4 : g (conj c * conj a * d * conj b) = conj a * d.
    Proof.
      pose (t := conj c * conj a * d).
      (** First cancel [conj b * b] on the right. *)
      refine (assoc c (t * conj b) b
        @ ap (.* b) (assoc c t (conj b))
        @ (assoc (c * t) (conj b) b)^
        @ ap ((c * t) *.) (left_inverse b)
        @ right_identity (c * t) @ _).
      (** Then cancel [c * conj c] on the left. *)
      exact (assoc c _ d
        @ ap (.* d) (assoc c (conj c) (conj a)
          @ ap (.* conj a) (right_inverse c))
        @ (assoc mon_unit (conj a) d)^
        @ left_identity (conj a * d)).
    Defined.

  End Lemmata.

  Arguments f {_ _}.
  Arguments g {_ _}.

  (** Here is the multiplication map in algebraic form: [(a,b) * (c,d) = (a * c - d * b*, a* * d + c * b)].  The following is the spherical form. *)
  #[export] Instance cd_op : SgOp (pjoin X X).
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
      (** Identify the scalar vertices using naturality of zigzags. *)
      napply (cancelL (ap joinl (lemma1 a c))).
      refine (zigzag_natsq (lemma1 a c) (lemma2 a b c d)
        (lemma4 a b c d) @ _
        @ (zigzag_natsq (lemma1 a c) (lemma2 a b c d)
          (lemma3 b c))^).
      (** The remaining comparison is the image of the chosen diamond. *)
      napply whiskerR.
      lhs_V napply (Join_rec_beta_zigzag _ _
        (fun x y => jglue (f x) (g y))).
      rhs_V napply (Join_rec_beta_zigzag _ _
        (fun x y => jglue (f x) (g y))).
      napply ap.
      exact (cd_diamond (conj c * conj a * d * conj b))^.
  Defined.

  #[export] Instance cd_op_left_identity
    : LeftIdentity cd_op pt.
  Proof.
    snapply Join_ind_Flr.
    1: exact (fun _ => ap joinl (hspace_left_identity _)).
    1: exact (fun b => ap joinr
      (ap (.* b) cds_conjug_unit_pres @ hspace_left_identity b)).
    intros a b.
    lhs napply (Join_rec_beta_jglue _ _ _ a b @@ 1).
    symmetry.
    apply join_natsq.
  Defined.

  #[export] Instance cd_op_right_identity
    : RightIdentity cd_op pt.
  Proof.
    snapply Join_ind_Flr.
    1: exact (fun _ => ap joinl (hspace_right_identity _)).
    1: exact (fun _ => ap joinr (hspace_left_identity _)).
    intros a b.
    lhs napply (Join_rec_beta_jglue _ _ _ a b @@ 1).
    simpl; symmetry.
    apply join_natsq.
  Defined.

  (** The diagonal inverse law only uses the one-glue computation rules. Its image is a zigzag with a common right vertex, so no symmetry of the chosen diamond is needed. *)
  #[export] Instance cd_op_conjugate_left_inverse
    : LeftInverse cd_op cd_conjugate pt.
  Proof.
    snapply Join_ind_FlFr.
    - intro a; exact (ap joinl (left_inverse a)).
    - intro b; exact (ap joinl (right_inverse (-b))).
    - intros a b.
      rhs napply (1 @@ ap_const _ _).
      rhs napply concat_p1.
      apply moveR_pM.
      rhs_V napply (ap_pV joinl).
      rhs_V napply (triangle_h' (B:=X) (conj (conj a) * b)).
      (** Compute the diagonal path by changing the second argument first. *)
      lhs_V napply (ap011_diag
        (fun x y => cd_op (cd_conjugate y) x) (jglue a b)).
      lhs napply (ap011_is_ap
        (fun x y => cd_op (cd_conjugate y) x)).
      napply concat2.
      + exact (Join_rec_beta_jglue _ _ _ a b).
      + lhs napply (ap_compose cd_conjugate
          (fun z => cd_op z (joinr b))).
        lhs napply (ap _ (functor_join_beta_jglue conj (-) a b)).
        exact (Join_rec_beta_jglue _ _ _ (conj a) (-b)).
  Defined.

  #[export] Instance cd_op_conjugate_right_inverse
    : RightInverse cd_op cd_conjugate pt.
  Proof.
    intro z.
    lhs_V exact (ap (fun w => cd_op w (cd_conjugate z))
      (involutive_cd_conjugate z)).
    apply cd_op_conjugate_left_inverse.
  Defined.

  #[export] Instance hspace_cd : IsHSpace (pjoin X X) := {}.

End SpheroidHSpace.

(** Resolve the inherited spheroid structure before searching for associativity. Ordinary instance search does not always unfold the inherited multiplication when matching the imaginaroid's associativity hypothesis. *)
#[export] Hint Extern 0 (IsHSpace (pjoin (psusp _) _))
  => rapply hspace_cd : typeclass_instances.

(** The original imaginaroid construction is the suspension instance of [hspace_cd]. *)
Notation hspace_cdi_susp_assoc := hspace_cd.
