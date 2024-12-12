Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Forall Types.Arrow Types.Sigma Cubical.DPath.
Require Import Homotopy.IdentitySystems.

(** * Quotient of a graph *)

(** ** Definition *)

(** The quotient of a graph is one of the simplest HITs that can be found in HoTT. It consists of a base type and a relation on it, and for every witness of a relation between two points of the type, a path.

We use graph quotients to build up all our other non-recursive HITs. Their simplicity means that we can easily prove results about them and generalise them to other HITs. *)

Local Unset Elimination Schemes.

Module Export GraphQuotient.
 Section GraphQuotient.

  Universes i j u.
  Constraint i <= u, j <= u.
  Context {A : Type@{i}}.

  Private Inductive GraphQuotient (R : A -> A -> Type@{j}) : Type@{u} :=
  | gq : A -> GraphQuotient R.

  Arguments gq {R} a.

  Context {R : A -> A -> Type@{j}}.

  Axiom gqglue : forall {a b : A},
    R a b -> paths (@gq R a) (gq b).

  Definition GraphQuotient_ind
    (P : GraphQuotient R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    : forall x, P x := fun x =>
    match x with
    | gq a => fun _ => gq' a
    end gqglue'.
  (** Above we did a match with output type a function, and then outside of the match we provided the argument [gqglue'].  If we instead end with [| gq a => gq' a end.], the definition will not depend on [gqglue'], which would be incorrect.  This is the idiom referred to in ../../test/bugs/github1758.v and github1759.v. *)

  Axiom GraphQuotient_ind_beta_gqglue
  : forall (P : GraphQuotient R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    (a b: A) (s : R a b),
    apD (GraphQuotient_ind P gq' gqglue') (gqglue s) = gqglue' a b s.

 End GraphQuotient.
End GraphQuotient.

Arguments gq {A R} a.

Definition GraphQuotient_rec {A R P} (c : A -> P) (g : forall a b, R a b -> c a = c b)
  : GraphQuotient R -> P.
Proof.
  srapply GraphQuotient_ind.
  1: exact c.
  intros a b s.
  refine (transport_const _ _ @ g a b s).
Defined.

Definition GraphQuotient_rec_beta_gqglue {A R P}
  (c : A -> P) (g : forall a b, R a b -> c a = c b)
  (a b : A) (s : R a b)
  : ap (GraphQuotient_rec c g) (gqglue s) = g a b s.
Proof.
  unfold GraphQuotient_rec.
  refine (cancelL _ _ _ _ ).
  refine ((apD_const _ _)^ @ _).
  rapply GraphQuotient_ind_beta_gqglue.
Defined.

(** ** Descent *)

(** We study "equifibrant" type families over a graph [A], with edges indexed by [R].  By univalence, the descent property tells us that these type families correspond to type families over the graph quotient, and we obtain an induction principle for such type families.  Dependent descent data over some particular descent data are "equifibrant" type families over this descent data.  The "equifibrancy" is only taken over the graph [A] and [R], but there is an extra level of dependency coming from the descent data.  In this case, we obtain an induction and recursion principle, but only with a computation rule for the recursion principle.

The theory of descent is interesting to consider in itself.  However, we will use it as a means to structure the code, and to obtain induction and recursion principles that are valuable in proving the flattening lemma, and characterizing path spaces.  Thus we will gloss over the bigger picture, and not consider equivalences of descent data, nor homotopies of their sections.  We will also not elaborate on uniqueness of the induced families.

It's possible to prove the results in the Descent, Flattening and Paths Sections without univalence, by replacing all equivalences with paths, but in practice these results will be used with equivalences as input, making the form below more convenient.  See https://github.com/HoTT/Coq-HoTT/pull/2147#issuecomment-2521570830 for further information. *)

Section Descent.

  Context `{Univalence}.

  (** Descent data over a graph [A] and [R] is an "equifibrant" or "cartesian" type family [gqd_fam : A -> Type].  If [a b : A] are related by [r : R a b], then the fibers [gqd_fam a] and [gqd_fam b] are equivalent, witnessed by [gqd_e]. *)
  Record gqDescent {A : Type} {R : A -> A -> Type} := {
    gqd_fam (a : A) : Type;
    gqd_e {a b : A} (r : R a b) : gqd_fam a <~> gqd_fam b
  }.

  Global Arguments gqDescent {A} R.

  (** Let [A] and [R] be a graph. *)
  Context {A : Type} {R : A -> A -> Type}.

  (** Descent data induces a type family over [GraphQuotient R]. *)
  Definition fam_gqdescent (Pe : gqDescent R)
    : GraphQuotient R -> Type.
  Proof.
    snrapply (GraphQuotient_rec (gqd_fam Pe)).
    intros a b r.
    exact (path_universe_uncurried (gqd_e Pe r)).
  Defined.

  (** A type family over [GraphQuotient R] induces descent data. *)
  Definition gqdescent_fam (P : GraphQuotient R -> Type) : gqDescent R.
  Proof.
    snrapply Build_gqDescent.
    - exact (P o gq).
    - intros a b r.
      exact (equiv_transport P (gqglue r)).
  Defined.

  (** Transporting over [fam_gqdescent] along [gqglue r] is given by [gqd_e]. *)
  Definition transport_fam_gqdescent_gqglue
    (Pe : gqDescent R) {a b : A} (r : R a b) (pa : gqd_fam Pe a)
    : transport (fam_gqdescent Pe) (gqglue r) pa = gqd_e Pe r pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply GraphQuotient_rec_beta_gqglue.
  Defined.

  (** A section on the descent data is a fiberwise section that respects the equivalences. *)
  Record gqDescentSection {Pe : gqDescent R} := {
    gqds_sect (a : A) : gqd_fam Pe a;
    gqds_e {a b : A} (r : R a b)
      : gqd_e Pe r (gqds_sect a) = gqds_sect b
  }.

  Global Arguments gqDescentSection Pe : clear implicits.

  (** A descent section induces a genuine section of [fam_gqdescent Pe]. *)
  Definition gqdescent_ind {Pe : gqDescent R}
    (f : gqDescentSection Pe)
    : forall (x : GraphQuotient R), fam_gqdescent Pe x.
  Proof.
    snrapply (GraphQuotient_ind _ (gqds_sect f)).
    intros a b r.
    exact (transport_fam_gqdescent_gqglue Pe r _ @ gqds_e f r).
  Defined.

  (** We record its computation rule *)
  Definition gqdescent_ind_beta_gqglue {Pe : gqDescent R}
    (f : gqDescentSection Pe) {a b : A} (r : R a b)
    : apD (gqdescent_ind f) (gqglue r) = transport_fam_gqdescent_gqglue Pe r _ @ gqds_e f r
    := GraphQuotient_ind_beta_gqglue _ (gqds_sect f) _ _ _ _.

  (** Dependent descent data over descent data [Pe : gqDescent R] consists of a type family [gqdd_fam : forall (a : A), gqd_fam Pe a -> Type] together with coherences [gqdd_e r pa]. *)
  Record gqDepDescent {Pe : gqDescent R} := {
    gqdd_fam (a : A) (pa : gqd_fam Pe a) : Type;
    gqdd_e {a b : A} (r :  R a b) (pa : gqd_fam Pe a)
      : gqdd_fam a pa <~> gqdd_fam b (gqd_e Pe r pa)
  }.

  Global Arguments gqDepDescent Pe : clear implicits.

  (** A dependent type family over [fam_gqdescent Pe] induces dependent descent data over [Pe]. *)
  Definition gqdepdescent_fam {Pe : gqDescent R}
    (Q : forall (x : GraphQuotient R), (fam_gqdescent Pe) x -> Type)
    : gqDepDescent Pe.
  Proof.
    snrapply Build_gqDepDescent.
    - intro a; cbn.
      exact (Q (gq a)).
    - intros a b r pa.
      exact (equiv_transportDD (fam_gqdescent Pe) Q
               (gqglue r) (transport_fam_gqdescent_gqglue Pe r pa)).
  Defined.

  (** Dependent descent data over [Pe] induces a dependent type family over [fam_gqdescent Pe]. *)
  Definition fam_gqdepdescent {Pe : gqDescent R} (Qe : gqDepDescent Pe)
    : forall (x : GraphQuotient R), (fam_gqdescent Pe x) -> Type.
  Proof.
    snrapply GraphQuotient_ind.
    - exact (gqdd_fam Qe).
    - intros a b r.
      nrapply (moveR_transport_p _ (gqglue r)).
      funext pa.
      rhs nrapply transport_arrow_toconst.
      rhs nrefine (ap (gqdd_fam Qe b) _).
      + exact (path_universe (gqdd_e Qe r pa)).
      + lhs nrapply (ap (fun x => (transport _ x _)) (inv_V (gqglue r))).
        nrapply (transport_fam_gqdescent_gqglue _ _ _).
  Defined.

  (** A section of dependent descent data [Qe : gqDepDescent Pe] is a fiberwise section [gqdds_sect], together with coherences [gqdd_e]. *)
  Record gqDepDescentSection {Pe : gqDescent R} {Qe : gqDepDescent Pe} := {
    gqdds_sect (a : A) (pa : gqd_fam Pe a) : gqdd_fam Qe a pa;
    gqdds_e {a b : A} (r : R a b) (pa : gqd_fam Pe a)
      : gqdd_e Qe r pa (gqdds_sect a pa) = gqdds_sect b (gqd_e Pe r pa)
  }.

  Global Arguments gqDepDescentSection {Pe} Qe.

  (** A dependent descent section induces a genuine section over the total space of [fam_gqdescent Pe]. *)
  Definition gqdepdescent_ind {Pe : gqDescent R}
    {Q : forall (x : GraphQuotient R), (fam_gqdescent Pe) x -> Type}
    (f : gqDepDescentSection (gqdepdescent_fam Q))
    : forall (x : GraphQuotient R) (px : fam_gqdescent Pe x), Q x px.
    Proof.
      nrapply (GraphQuotient_ind _ (gqdds_sect f) _).
      intros a b r.
      apply dpath_forall.
      intro pa.
      apply (equiv_inj (transport (Q (gq b)) (transport_fam_gqdescent_gqglue Pe r pa))).
      rhs nrapply (apD (gqdds_sect f b) (transport_fam_gqdescent_gqglue Pe r pa)).
      exact (gqdds_e f r pa).
    Defined.

  (** The data for a section into a constant type family. *)
  Record gqDepDescentConstSection {Pe : gqDescent R} {Q : Type} := {
    gqddcs_sect (a : A) (pa : gqd_fam Pe a) : Q;
    gqddcs_e {a b : A} (r : R a b) (pa : gqd_fam Pe a)
      : gqddcs_sect a pa = gqddcs_sect b (gqd_e Pe r pa)
  }.

  Global Arguments gqDepDescentConstSection Pe Q : clear implicits.

  (** The data for a section of a constant family induces a section over the total space of [fam_gqdescent Pe]. *)
  Definition gqdepdescent_rec {Pe : gqDescent R} {Q : Type}
    (f : gqDepDescentConstSection Pe Q)
    : forall (x : GraphQuotient R), fam_gqdescent Pe x -> Q.
  Proof.
    snrapply (GraphQuotient_ind _ (gqddcs_sect f)).
    intros a b r.
    nrapply dpath_arrow.
    intro pa.
    lhs nrapply transport_const.
    rhs nrapply (ap _ (transport_fam_gqdescent_gqglue Pe r pa)).
    exact (gqddcs_e f r pa).
  Defined.

  (** Here is the computation rule on paths. *)
  Definition gqdepdescent_rec_beta_gqglue {Pe : gqDescent R} {Q : Type}
    (f : gqDepDescentConstSection Pe Q)
    {a b : A} {pa : gqd_fam Pe a} {pb : gqd_fam Pe b} (r : R a b) (pr : gqd_e Pe r pa = pb)
    : ap (sig_rec (gqdepdescent_rec f)) (path_sigma _ (gq a; pa) (gq b; pb) (gqglue r) (transport_fam_gqdescent_gqglue Pe r pa @ pr))
      = gqddcs_e f r pa @ ap (gqddcs_sect f b) pr.
  Proof.
    Open Scope long_path_scope.
    destruct pr.
    rhs nrapply concat_p1.
    lhs nrapply ap_sig_rec_path_sigma.
    lhs nrapply (ap (fun x => _ (ap10 x _) @ _)).
    1: nrapply GraphQuotient_ind_beta_gqglue.
    do 3 lhs nrapply concat_pp_p.
    apply moveR_Vp.
    lhs nrefine (1 @@ (1 @@ (_ @@ 1))).
    1: nrapply (ap10_dpath_arrow (fam_gqdescent Pe) (fun _ => Q) (gqglue r)).
    lhs nrefine (1 @@ _).
    { lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      lhs nrapply concat_V_pp.
      lhs nrapply (1 @@ concat_pp_p _ _ _).
      rewrite concat_p1.
      nrapply (1 @@ (1 @@ concat_pV_p _ _)). }
    nrapply concat_V_pp.
    Close Scope long_path_scope.
  Defined.

End Descent.

(** ** The flattening lemma *)

(** We saw above that given descent data [Pe] over a graph [A] and [R] we obtained a type family [fam_gqdescent Pe] over the graph quotient.  The flattening lemma describes the total space [sig (fam_gqdescent Pe)] of this type family as a graph quotient of [sig (gqd_fam Pe)] by a certain relation.  This follows from the work above, which shows that [sig (fam_gqdescent Pe)] has the same universal property as this graph quotient. *)

Section Flattening.

  Context `{Univalence} {A : Type} {R : A -> A -> Type} (Pe : gqDescent R).

  (** We mimic the constructors of [GraphQuotient] for the total space.  Here is the point constructor, in curried form. *)
  Definition flatten_gqd {a : A} (pa : gqd_fam Pe a) : sig (fam_gqdescent Pe)
    := (gq a; pa).

  (** And here is the path constructor. *)
  Definition flatten_gqd_glue {a b : A} (r : R a b)
    {pa : gqd_fam Pe a} {pb : gqd_fam Pe b} (pr : gqd_e Pe r pa = pb)
    : flatten_gqd pa = flatten_gqd pb.
  Proof.
    snrapply path_sigma.
    - by apply gqglue.
    - lhs nrapply transport_fam_gqdescent_gqglue.
      exact pr.
  Defined.

  (** Now that we've shown that [fam_gqdescent Pe] acts like a [GraphQuotient] of [sig (gqd_fam Pe)] by an appropriate relation, we can use this to prove the flattening lemma.  The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *)
  Lemma equiv_gqd_flatten : sig (fam_gqdescent Pe) <~>
    GraphQuotient (fun a b => {r : R a.1 b.1 & gqd_e Pe r a.2 = b.2}).
  Proof.
    snrapply equiv_adjointify.
    - snrapply sig_rec.
      snrapply gqdepdescent_rec.
      snrapply Build_gqDepDescentConstSection.
      + exact (fun a x => gq (a; x)).
      + intros a b r pa.
      apply gqglue; exact (r; 1).
    - snrapply GraphQuotient_rec.
      + exact (fun '(a; x) => (gq a; x)).
      + intros [a x] [b y] [r pr]; cbn in r, pr; cbn.
        apply (flatten_gqd_glue r pr).
    - snrapply GraphQuotient_ind.
      1: reflexivity.
      intros [a x] [b y] [r pr]; cbn in r, pr; cbn.
      destruct pr.
      nrapply transport_paths_FFlr'; apply equiv_p1_1q.
      rewrite GraphQuotient_rec_beta_gqglue.
      lhs nrapply gqdepdescent_rec_beta_gqglue.
      nrapply concat_p1.
    - intros [x px]; revert x px.
      snrapply gqdepdescent_ind.
      snrapply Build_gqDepDescentSection.
      + by intros a pa.
      + intros a b r pa; cbn.
        lhs nrapply transportDD_is_transport.
        nrapply transport_paths_FFlr'; apply equiv_p1_1q.
        rewrite <- (concat_p1 (transport_fam_gqdescent_gqglue _ _ _)).
        rewrite gqdepdescent_rec_beta_gqglue. (* This needs to be in the form [transport_fam_gqdescent_gqglue Pe r pa @ p] to work, and the other [@ 1] introduced comes in handy as well. *)
        lhs nrapply (ap _ (concat_p1 _)).
        nrapply (GraphQuotient_rec_beta_gqglue _ _ (a; pa) (b; _) (r; 1)).
  Defined.

End Flattening.

(** ** Characterization of path spaces*)

(** A pointed type family over a graph quotient has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)

Section Paths.

  (** Let [A] and [R] be a graph, with a distinguished point [a0 : A].  Let [Pe : gqDescent R] be descent data over [A] and [R] with a distinguished point [p0 : gqd_fam Pe a0].  Assume that any dependent descent data [Qe : gqDepDescent Pe] with a distinguished point [q0 : gqdd_fam Qe a0 p0] has a section that respects the distinguished points.  This is the induction principle provided by Kraus and von Raumer. *)
  Context `{Univalence} {A : Type} {R : A -> A -> Type} (a0 : A)
    (Pe : gqDescent R) (p0 : gqd_fam Pe a0)
    (based_gqdepdescent_ind : forall (Qe : gqDepDescent Pe) (q0 : gqdd_fam Qe a0 p0),
      gqDepDescentSection Qe)
    (based_gqdepdescent_ind_beta : forall (Qe : gqDepDescent Pe) (q0 : gqdd_fam Qe a0 p0),
      gqdds_sect (based_gqdepdescent_ind Qe q0) a0 p0 = q0).

  (** Under these hypotheses, we get an identity system structure on [fam_gqdescent Pe]. *)
  Local Instance idsys_flatten_gqdescent
    : @IsIdentitySystem _ (gq a0) (fam_gqdescent Pe) p0.
  Proof.
    snrapply Build_IsIdentitySystem.
    - intros Q q0 x p.
      snrapply gqdepdescent_ind.
      by apply based_gqdepdescent_ind.
    - intros Q q0; cbn.
      nrapply (based_gqdepdescent_ind_beta (gqdepdescent_fam Q)).
  Defined.

  (** It follows that the fibers [fam_gqdescent Pe x] are equivalent to path spaces [(gq a0) = x]. *)
  Definition fam_gqdescent_equiv_path (x : GraphQuotient R)
    : (gq a0) = x <~> fam_gqdescent Pe x
    := @equiv_transport_identitysystem _ (gq a0) (fam_gqdescent Pe) p0 _ x.

End Paths.

(** ** Functoriality of graph quotients *)

Lemma functor_gq {A B : Type} (f : A -> B)
  {R : A -> A -> Type} {S : B -> B -> Type} (e : forall a b, R a b -> S (f a) (f b))
  : GraphQuotient R -> GraphQuotient S.
Proof.
  snrapply GraphQuotient_rec.
  1: exact (fun x => gq (f x)).
  intros a b r.
  apply gqglue.
  apply e.
  exact r.
Defined.

Lemma functor_gq_idmap {A : Type} {R : A -> A -> Type}
  : functor_gq (A:=A) (B:=A) (S:=R) idmap (fun a b r => r) == idmap.
Proof.
  snrapply GraphQuotient_ind.
  1: reflexivity.
  intros a b r.
  nrapply (transport_paths_FlFr' (gqglue r)).
  apply equiv_p1_1q.
  rhs nrapply ap_idmap.
  nrapply GraphQuotient_rec_beta_gqglue.
Defined.

Lemma functor_gq_compose {A B C : Type} (f : A -> B) (g : B -> C)
  {R : A -> A -> Type} {S : B -> B -> Type} {T : C -> C -> Type}
  (e : forall a b, R a b -> S (f a) (f b)) (e' : forall a b, S a b -> T (g a) (g b))
  : functor_gq g e' o (functor_gq f e) == functor_gq (g o f) (fun a b r => e' _ _ (e _ _ r)).
Proof.
  snrapply GraphQuotient_ind.
  1: reflexivity.
  intros a b s.
  nrapply (transport_paths_FlFr' (gqglue s)).
  apply equiv_p1_1q.
  lhs nrapply (ap_compose (functor_gq f e) (functor_gq g e') (gqglue s)).
  lhs nrapply ap.
  1: apply GraphQuotient_rec_beta_gqglue.
  lhs nrapply GraphQuotient_rec_beta_gqglue.
  exact (GraphQuotient_rec_beta_gqglue _ _ _ _ s)^.
Defined.

Lemma functor2_gq {A B : Type} (f f' : A -> B)
  {R : A -> A -> Type} {S : B -> B -> Type}
  (e : forall a b, R a b -> S (f a) (f b)) (e' : forall a b, R a b -> S (f' a) (f' b))
  (p : f == f')
  (q : forall a b r, transport011 S (p a) (p b) (e a b r) = e' a b r)
  : functor_gq f e == functor_gq f' e'.
Proof.
  snrapply GraphQuotient_ind.
  - simpl; intro.
    apply ap.
    apply p.
  - intros a b s.
    nrapply (transport_paths_FlFr' (gqglue s)).
    rhs nrefine (1 @@ _).
    2: apply GraphQuotient_rec_beta_gqglue.
    lhs nrefine (_ @@ 1).
    1: apply GraphQuotient_rec_beta_gqglue.
    apply moveL_Mp.
    symmetry.
    destruct (q a b s).
    lhs nrapply (ap_transport011 _ _ (fun s _ => gqglue)).
    rhs nrapply concat_p_pp.
    nrapply transport011_paths.
Defined.

(** ** Equivalence of graph quotients *)

Global Instance isequiv_functor_gq {A B : Type} (f : A -> B) `{IsEquiv _ _ f}
  {R : A -> A -> Type} {S : B -> B -> Type} (e : forall a b, R a b -> S (f a) (f b))
  `{forall a b, IsEquiv (e a b)}
  : IsEquiv (functor_gq f e).
Proof.
  srapply isequiv_adjointify.
  - nrapply (functor_gq f^-1).
    intros a b s.
    apply (e _ _)^-1.
    exact (transport011 S (eisretr f a)^ (eisretr f b)^ s).
  - intros x.
    lhs nrapply functor_gq_compose.
    rhs_V nrapply functor_gq_idmap.
    snrapply functor2_gq; cbn beta.
    1: apply eisretr.
    intros a b s.
    rewrite (eisretr (e (f^-1 a) (f^-1 b))).
    lhs_V nrapply transport011_pp.
    by rewrite 2 concat_Vp.
  - intros x.
    lhs nrapply functor_gq_compose.
    rhs_V nrapply functor_gq_idmap.
    snrapply functor2_gq; cbn beta.
    1: apply eissect.
    intros a b r.
    rewrite 2 eisadj.
    rewrite <- 2 ap_V.
    rewrite <- (transport011_compose S).
    rewrite <- (ap_transport011 (Q := fun x y => S (f x) (f y)) (eissect f a)^ (eissect f b)^ e).
    rewrite (eissect (e (f^-1 (f a)) (f^-1 (f b)))).
    lhs_V nrapply transport011_pp.
    by rewrite 2 concat_Vp.
Defined.

Definition equiv_functor_gq {A B : Type} (f : A <~> B)
  (R : A -> A -> Type) (S : B -> B -> Type) (e : forall a b, R a b <~> S (f a) (f b))
  : GraphQuotient R <~> GraphQuotient S
  := Build_Equiv _ _ (functor_gq f e) _.
