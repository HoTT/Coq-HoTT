Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Types.Forall Cubical.DPath.

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

(** ** The flattening lemma *)

(** Univalence tells us that type families over a colimit correspond to cartesian families over the indexing diagram.  The flattening lemma gives an explicit description of the family over a colimit that corresponds to a given cartesian family, again using univalence.  Together, these are known as descent, a fundamental result in higher topos theory which has many implications. *)

Section Flattening.
  
  Context `{Univalence} {A : Type} {R : A -> A -> Type}.
  (** We consider a type family over [A] which is "equifibrant" or "cartesian": the fibers are equivalent when the base points are related by [R]. *)
  Context (F : A -> Type) (e : forall x y, R x y -> F x <~> F y).

  (** By univalence, the equivalences give equalities, which means that [F] induces a map on the quotient. *)
  Definition DGraphQuotient : GraphQuotient R -> Type
    := GraphQuotient_rec F (fun x y s => path_universe (e x y s)).

  (** The transport of [DGraphQuotient] along [gqglue] equals the equivalence [e] applied to the original point. This lemma is required a few times in the following proofs. *)
  Definition transport_DGraphQuotient {x y} (s : R x y) (a : F x)
    : transport DGraphQuotient (gqglue s) a = e x y s a.
  Proof.
    lhs nrapply transport_idmap_ap.
    lhs nrapply (transport2 idmap).
    1: apply GraphQuotient_rec_beta_gqglue.
    rapply transport_path_universe.
  Defined.

  (** The family [DGraphQuotient] we have defined over [GraphQuotient R] has a total space which we will describe as a [GraphQuotient] of [sig F] by an appropriate relation. *)

  (** We mimic the constructors of [GraphQuotient] for the total space. Here is the point constructor. *)
  Definition flatten_gq {x} : F x -> sig DGraphQuotient.
  Proof.
    intros p.
    exact (gq x; p).
  Defined.
  
  (** And here is the path constructor. *)
  Definition flatten_gqglue {x y} (s : R x y) (a : F x)
    : flatten_gq a = flatten_gq (e x y s a).
  Proof.
    snrapply path_sigma'.
    - by apply gqglue.
    - apply transport_DGraphQuotient.
  Defined.

  (** This lemma is the same as [transport_DGraphQuotient] but adapted instead for [DPath]. The use of [DPath] will be apparent there. *)
  Lemma equiv_dp_dgraphquotient (x y : A) (s : R x y) (a : F x) (b : F y)
    : DPath DGraphQuotient (gqglue s) a b <~> (e x y s a = b).
  Proof.
    refine (equiv_concat_l _^ _).
    apply transport_DGraphQuotient.
  Defined.

  (** We can also prove an induction principle for [sig DGraphQuotient]. We won't show that it satisfies the relevant computation rules as these will not be needed. Instead we will prove the non-dependent eliminator directly so that we can better reason about it. In order to get through the path algebra here, we have opted to use dependent paths. This makes the reasoning slightly easier, but it should not matter too much. *)
  Definition flatten_ind {Q : sig DGraphQuotient -> Type}
    (Qgq : forall a (x : F a), Q (flatten_gq x))
    (Qgqglue : forall a b (s : R a b) (x : F a),
      flatten_gqglue s x # Qgq _ x = Qgq _ (e _ _ _ x))
    : forall x, Q x.
  Proof.
    apply sig_ind.
    snrapply GraphQuotient_ind.
    1: exact Qgq.
    intros a b s.
    apply dp_forall.
    intros x y.
    srapply (equiv_ind (equiv_dp_dgraphquotient a b s x y)^-1).
    intros q.
    destruct q.
    refine (transport2 _ _ _ @ Qgqglue a b s x).
    refine (ap (path_sigma_uncurried DGraphQuotient _ _) _).
    snrapply path_sigma.
    1: reflexivity.
    lhs nrapply concat_p1.
    apply inv_V.
  Defined.

  (** Rather than use [flatten_ind] to define [flatten_rec] we reprove this simple case. This means we can later reason about it and derive the computation rules easily. The full computation rule for [flatten_ind] takes some work to derive and is not actually needed. *)
  Definition flatten_rec {Q : Type} (Qgq : forall a, F a -> Q)
    (Qgqglue : forall a b (s : R a b) (x : F a), Qgq a x = Qgq b (e _ _ s x))
    : sig DGraphQuotient -> Q.
  Proof.
    apply sig_rec.
    snrapply GraphQuotient_ind.
    1: exact Qgq.
    intros a b s.
    nrapply dpath_arrow.
    intros y.
    lhs nrapply transport_const.
    lhs nrapply (Qgqglue a b s).
    f_ap; symmetry.
    apply transport_DGraphQuotient.
  Defined.

  (** The non-dependent eliminator computes as expected on our "path constructor". *) 
  Definition flatten_rec_beta_gqglue {Q : Type} (Qgq : forall a, F a -> Q)
    (Qgqglue : forall a b (r : R a b) (x : F a), Qgq a x = Qgq b (e _ _ r x))
    (a b : A) (s : R a b) (x : F a)
    : ap (flatten_rec Qgq Qgqglue) (flatten_gqglue s x) = Qgqglue a b s x.
  Proof.
    lhs nrapply ap_sig_rec_path_sigma; cbn.
    lhs nrapply (ap (fun x => x @ _)).
    { nrapply ap.
      nrapply (ap01 (fun x => ap10 x _)).
      nrapply GraphQuotient_ind_beta_gqglue. }
    apply moveR_pM.
    apply moveL_pM.
    do 3 lhs nrapply concat_pp_p.
    apply moveR_Vp.
    lhs refine (1 @@ (1 @@ (_ @@ 1))).
    1: nrapply (ap10_dpath_arrow DGraphQuotient (fun _ => Q) (gqglue s)).
    lhs refine (1 @@ (1 @@ _)).
    { lhs nrapply concat_pp_p.
      nrapply concat_pp_p. }
    lhs nrapply (1 @@ concat_V_pp _ _).
    lhs nrapply concat_V_pp.
    lhs nrapply concat_pp_p.
    f_ap.
    lhs nrapply concat_pp_p.
    apply moveR_Mp.
    rhs nrapply concat_Vp.
    apply moveR_pV.
    rhs nrapply concat_1p.
    nrapply ap_V.
  Defined.

  (** Now that we've shown that [sig DGraphQuotient] acts like a [GraphQuotient] of [sig F] by an appropriate relation, we can use this to prove the flattening lemma. The maps back and forth are very easy so this could almost be a formal consequence of the induction principle. *) 
  Lemma equiv_gq_flatten
    : sig DGraphQuotient
    <~> GraphQuotient (fun a b => {r : R a.1 b.1 & e _ _ r a.2 = b.2}).
  Proof.
    snrapply equiv_adjointify.
    - snrapply flatten_rec.
      + exact (fun a x => gq (a; x)).
      + intros a b r x.
        apply gqglue.
        exists r.
        reflexivity.
    - snrapply GraphQuotient_rec.
      + exact (fun '(a; x) => (gq a; x)).
      + intros [a x] [b y] [r p].
        simpl in p, r.
        destruct p.
        apply flatten_gqglue.
    - snrapply GraphQuotient_ind.
      1: reflexivity.
      intros [a x] [b y] [r p].
      simpl in p, r.
      destruct p.
      simpl.
      lhs nrapply transport_paths_FFlr.
      rewrite GraphQuotient_rec_beta_gqglue.
      refine ((_ @@ 1) @ concat_Vp _).
      lhs nrapply concat_p1.
      apply inverse2.
      nrapply flatten_rec_beta_gqglue.
    - snrapply flatten_ind.
      1: reflexivity.
      intros a b r x.
      nrapply (transport_paths_FFlr' (g := GraphQuotient_rec _ _)); apply equiv_p1_1q.
      rewrite flatten_rec_beta_gqglue.
      exact (GraphQuotient_rec_beta_gqglue _ _ (a; x) (b; e a b r x) (r; 1)).
  Defined.

End Flattening.

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
