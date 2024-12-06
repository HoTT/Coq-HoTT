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

(** We study "equifibrant" type families over a graph [A], with edges indexed by [R]. By univalence, the descent property tells us that these type families correspond to type families over the graph quotient, and we obtain an induction principle for such type families. Then we consider dependent descent data over some particular descent data. This resembles the first case, but there is an extra level of dependence. In this case we obtain an induction and recursion principle, but only with a partial computation rule for the induction principle.

It's possible to prove the results in the Descent, Flattening and Paths Sections without univalence, by replacing all equivalences with paths, but in practice these results will be used with equivalences as input, making the form below more convenient.  See https://github.com/HoTT/Coq-HoTT/pull/2147#issuecomment-2521570830 for further information. *)

Section Descent.

  Context `{Univalence}.

  (** Descent data over a graph [A] and [R] is an "equifibrant" or "cartesian" type family [gqd_fam : A -> Type]. This means that if [a b : A] are related by [r : R a b], then the fibers [gqd_fam a] and [gqd_fam b] are equivalent, witnessed by [gqd_e]. *)
  Record gqDescent {A : Type} (R : A -> A -> Type) := {
    gqd_fam : A -> Type;
    gqd_e {a b : A} : R a b -> gqd_fam a <~> gqd_fam b
  }.

  Global Arguments Build_gqDescent {A R} gqd_fam gqd_e.
  Global Arguments gqd_fam {A R} Pe a : rename.
  Global Arguments gqd_e {A R} Pe {a b} r : rename.

  (** Let [A] and [R] be a graph.  *)
  Context {A : Type} {R : A -> A -> Type}.

  (** Descent data induces a type family over [GraphQuotient R]. *)
  Definition induced_fam_gqd (Pe : gqDescent R)
    : GraphQuotient R -> Type.
  Proof.
    snrapply (GraphQuotient_rec (gqd_fam Pe)).
    intros a b r.
    exact (path_universe_uncurried (gqd_e Pe r)).
  Defined.

  (** Transporting over [induced_fam_gqd] along [gqglue r] is given by [gqd_e]. *)
  Definition transport_induced_fam_gqd_gqglue
    (Pe : gqDescent R) {a b : A} (r : R a b) (pa : gqd_fam Pe a)
    : transport (induced_fam_gqd Pe) (gqglue r) pa = gqd_e Pe r pa.
  Proof.
    nrapply transport_path_universe'.
    nrapply GraphQuotient_rec_beta_gqglue.
  Defined.

  (** A section on the descent data is a fiberwise section that respects the equivalence. *)
  Record gqDescentSection (Pe : gqDescent R) := {
    gqds_sect (a : A) : gqd_fam Pe a;
    gqds_e {a b : A} (r : R a b)
      : gqd_e Pe r (gqds_sect a) = gqds_sect b
  }.

  (** A descent section induces a genuine section of [induced_fam_gqd Pe]. *)
  Definition gqdescent_ind {Pe : gqDescent R}
    (f : gqDescentSection Pe)
    : forall (x : GraphQuotient R), induced_fam_gqd Pe x.
  Proof.
    snrapply (GraphQuotient_ind _ (gqds_sect _ f)).
    intros a b r.
    refine (transport_induced_fam_gqd_gqglue Pe r _ @ gqds_e _ f r).
  Defined.

  (** We record its computation rule *)
  Definition gqdescent_ind_beta_gqglue {Pe : gqDescent R}
    (f : gqDescentSection Pe) {a b : A} (r : R a b)
    : apD (gqdescent_ind f) (gqglue r) = transport_induced_fam_gqd_gqglue Pe r _ @ gqds_e _ f r
    := GraphQuotient_ind_beta_gqglue _ (gqds_sect _ f) _ _ _ _.

  (** Dependent descent data over descent data [Pe : gqDescent R] consists of a type family [gqdd_fam : forall a : A, gqd_fam Pe a -> Type] together with coherences [gqdd_e r pa]. *)
  Record gqDepDescent (Pe : gqDescent R) := {
    gqdd_fam (a : A) : gqd_fam Pe a -> Type;
    gqdd_e {a b : A} (r :  R a b) (pa : gqd_fam Pe a)
      : gqdd_fam a pa <~> gqdd_fam b (gqd_e Pe r pa)
  }.

  Global Arguments Build_gqDepDescent {Pe} gqdd_fam gqdd_e.
  Global Arguments gqdd_fam {Pe} Qe a pa : rename.
  Global Arguments gqdd_e {Pe} Qe {a b} r pa : rename.

  (** A dependent type family over [induced_fam_gqd Pe] induces dependent descent data over [Pe]. *)
  Definition induced_fam_gqdd {Pe : gqDescent R}
    (Q : forall x : GraphQuotient R, (induced_fam_gqd Pe) x -> Type)
    : gqDepDescent Pe.
  Proof.
    snrapply Build_gqDepDescent.
    - intro a; cbn.
      exact (Q (gq a)).
    - intros a b r pa.
      exact (equiv_transportDD (induced_fam_gqd Pe) Q
               (gqglue r) (transport_induced_fam_gqd_gqglue Pe r pa)).
  Defined.

  (** A section of dependent descent data [Qe : gqDepDescent Pe] is a fiberwise section [gqdds_sect], together with coherences [gqdd_e]. *)
  Record gqDepDescentSection {Pe : gqDescent R} (Qe : gqDepDescent Pe) := {
    gqdds_sect (a : A) (pa : gqd_fam Pe a) : gqdd_fam Qe a pa;
    gqdds_e {a b : A} (r : R a b) (pa : gqd_fam Pe a)
      : gqdd_e Qe r pa (gqdds_sect a pa) = gqdds_sect b (gqd_e Pe r pa)
  }.

  Global Arguments Build_gqDepDescentSection {Pe Qe} gqdds_sect gqdds_e.
  Global Arguments gqdds_sect {Pe Qe} f a pa : rename.
  Global Arguments gqdds_e {Pe Qe} f {a b} r pa : rename.

  (** Transporting [gqdds_sect f a] over [Q] along [gqglue r] is [gqdds_sect f b]. *)
  Definition transport_gqds_gqglue {Pe : gqDescent R}
    {Q : forall x : GraphQuotient R, (induced_fam_gqd Pe) x -> Type}
    (f : gqDepDescentSection (induced_fam_gqdd Q))
    (a b : A) (r : R a b)
    : transport (fun x : GraphQuotient R => forall px : induced_fam_gqd Pe x, Q x px)
        (gqglue r) (gqdds_sect f a) = gqdds_sect f b.
  Proof.
    apply dpath_forall.
    intro pa.
    apply (equiv_inj (transport (Q (gq b)) (transport_induced_fam_gqd_gqglue Pe r pa))).
    rhs nrapply (apD (gqdds_sect f b) (transport_induced_fam_gqd_gqglue Pe r pa)).
    exact (gqdds_e f r pa).
  Defined.

  (** A dependent descent section induces a genuine section on the total space of [induced_fam_gqd Pe]. *)
  Definition gqdepdescent_ind {Pe : gqDescent R}
    {Q : forall x : GraphQuotient R, (induced_fam_gqd Pe) x -> Type}
    (f : gqDepDescentSection (induced_fam_gqdd Q))
    : forall (x : GraphQuotient R) (px : induced_fam_gqd Pe x), Q x px
    := GraphQuotient_ind _ (gqdds_sect f) (transport_gqds_gqglue f).

  (** This is a partial computation rule, which only handles paths in the base. *)
  Definition gqdepdescent_ind_beta_gqglue {Pe : gqDescent R}
    {Q : forall x, (induced_fam_gqd Pe) x -> Type}
    (f : gqDepDescentSection (induced_fam_gqdd Q))
    {a b : A} (r : R a b)
    : apD (gqdepdescent_ind f) (gqglue r) = transport_gqds_gqglue f a b r
    := GraphQuotient_ind_beta_gqglue _ (gqdds_sect f) (transport_gqds_gqglue f) a b r.

  (** The data for a section into a constant type family. *)
  Record gqDepDescentConstSection (Pe : gqDescent R) (Q : Type) := {
    gqdcs_sect (a : A) : gqd_fam Pe a -> Q;
    gqdcs_e {a b : A} (r : R a b) (pa : gqd_fam Pe a)
      : gqdcs_sect a pa = gqdcs_sect b (gqd_e Pe r pa)
  }.

  Global Arguments Build_gqDepDescentConstSection {Pe Q} gqdcs_sect gqdcs_e.
  Global Arguments gqdcs_sect {Pe Q} f a pa : rename.
  Global Arguments gqdcs_e {Pe Q} f {a b} r pa : rename.

  (** Transporting [gqdcs_sect f a] over [Q] along [gqglue r] is [gdcs_sect f b]. *)
  Definition transport_gqdcs_gqglue {Pe : gqDescent R} {Q : Type}
    (f : gqDepDescentConstSection Pe Q)
    {a b : A} (r : R a b)
    : transport (fun x : GraphQuotient R => induced_fam_gqd Pe x -> Q) (gqglue r) (gqdcs_sect f a)
      = gqdcs_sect f b.
  Proof.
    nrapply dpath_arrow.
    intro pa.
    lhs nrapply transport_const.
    rhs nrapply (ap _ (transport_induced_fam_gqd_gqglue Pe r pa)).
    exact (gqdcs_e f r pa).
  Defined.

  (** The data for a section of a constant family induces a section over the total space of [induced_fam_gqd Pe]. *)
  Definition gqdepdescent_rec {Pe : gqDescent R} {Q : Type}
    (f : gqDepDescentConstSection Pe Q)
    : forall (x : GraphQuotient R), induced_fam_gqd Pe x -> Q.
  Proof.
    snrapply GraphQuotient_ind; cbn.
    - nrapply (gqdcs_sect f).
    - nrapply transport_gqdcs_gqglue.
  Defined.

  (** In this case, we state a full computation rule. *)
  Definition gqdepdescent_rec_beta_gqglue {Pe : gqDescent R} {Q : Type}
    (f : gqDepDescentConstSection Pe Q)
    {a b : A} {pa : gqd_fam Pe a} {pb : gqd_fam Pe b} (r : R a b) (pr : gqd_e Pe r pa = pb)
    : ap (sig_rec (gqdepdescent_rec f)) (path_sigma _ (gq a; pa) (gq b; pb) (gqglue r) (transport_induced_fam_gqd_gqglue Pe r pa @ pr))
      = gqdcs_e f r pa @ ap (gqdcs_sect f b) pr.
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
    1: nrapply (ap10_dpath_arrow (induced_fam_gqd Pe) (fun _ => Q) (gqglue r)).
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

(** We saw above that given descent data [Pe] over a graph [A] and [R] we obtained a type family [induced_fam_gqd Pe] over the graph quotient. The flattening lemma describes the total space [sig (induced_fam_gqd Pe)] of this type family as a graph quotient of [sig (gqd_fam Pe)] by a certain relation.  This follows from the work above, which shows that [sig (induced_fam_gqd Pe)] has the same universal property as this graph quotient. *)

Section Flattening.

  Context `{Univalence} {A : Type} {R : A -> A -> Type} (Pe : gqDescent R).

  (** We mimic the constructors of [GraphQuotient] for the total space. Here is the point constructor, in curried form. *)
  Definition flatten_gqd {a : A} (pa : gqd_fam Pe a) : sig (induced_fam_gqd Pe)
    := (gq a; pa).

  (** And here is the path constructor. *)
  Definition flatten_gqd_glue {a b : A} (r : R a b)
    {pa : gqd_fam Pe a} {pb : gqd_fam Pe b} (pr : gqd_e Pe r pa = pb)
    : flatten_gqd pa = flatten_gqd pb.
  Proof.
    snrapply path_sigma.
    - by apply gqglue.
    - lhs nrapply transport_induced_fam_gqd_gqglue.
      exact pr.
  Defined.

  (** Now that we've shown that [induced_fam_gqd Pe] acts like a [GraphQuotient] of [sig (gqd_fam Pe)] by an appropriate relation, we can use this to prove the flattening lemma. The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *)
  Lemma equiv_gqd_flatten : sig (induced_fam_gqd Pe) <~>
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
        rewrite <- (concat_p1 (transport_induced_fam_gqd_gqglue _ _ _)).
        rewrite gqdepdescent_rec_beta_gqglue. (* This needs to be in the form [transport_induced_fam_gqd_gqglue Pe r pa @ p] to work, and the other [@ 1] introduced comes in handy as well. *)
        lhs nrapply (ap _ (concat_p1 _)).
        nrapply (GraphQuotient_rec_beta_gqglue _ _ (a; pa) (b; _) (r; 1)).
  Defined.

End Flattening.

(** ** Characterization of path spaces*)

(** A pointed type family over a graph quotient has an identity system structure precisely when its associated descent data satisfies Kraus and von Raumer's induction principle, https://arxiv.org/pdf/1901.06022. *)

Section Paths.

  (** Let [A] and [R] be a graph, with a distinguished point [a0 : A]. Let [Pe : gqDescent R] be descent data over [A] and [R] with a distinguished point [p0 : gqd_fam Pe a0]. Assume that any dependent descent data [Qe : gqDepDescent Pe] with a distinguished point [q0 : gqdd_fam Qe a0 p0] has a section that respects the distinguished points. This is the Kraus-von Raumer induction principle. *)
  Context `{Univalence} {A : Type} {R : A -> A -> Type} (a0 : A)
    (Pe : gqDescent R) (p0 : gqd_fam Pe a0)
    (based_gqdepdescent_ind : forall (Qe : gqDepDescent Pe) (q0 : gqdd_fam Qe a0 p0),
      gqDepDescentSection Qe)
    (based_gqdepdescent_ind_beta : forall (Qe : gqDepDescent Pe) (q0 : gqdd_fam Qe a0 p0),
      gqdds_sect (based_gqdepdescent_ind Qe q0) a0 p0 = q0).

  (** Under these hypotheses, we get an identity system structure on [induced_fam_gqd Pe]. *)
  Local Instance idsys_flatten_gqdescent
    : @IsIdentitySystem _ (gq a0) (induced_fam_gqd Pe) p0.
  Proof.
    snrapply Build_IsIdentitySystem.
    - intros Q q0 x p.
      snrapply gqdepdescent_ind.
      by apply based_gqdepdescent_ind.
    - intros Q q0; cbn.
      nrapply (based_gqdepdescent_ind_beta (induced_fam_gqdd Q)).
  Defined.

  (** It follows that the fibers [induced_fam_gqd Pe x] are equivalent to path spaces [(gq a0) = x]. *)
  Definition induced_fam_gqd_equiv_path (x : GraphQuotient R)
    : (gq a0) = x <~> induced_fam_gqd Pe x
    := @equiv_transport_identitysystem _ (gq a0) (induced_fam_gqd Pe) p0 _ x.

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
