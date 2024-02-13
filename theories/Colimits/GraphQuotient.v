Require Import Basics.Overture Basics.Tactics Basics.PathGroupoids Basics.Equivalences.
Require Import Types.Universe Types.Paths Types.Arrow Types.Sigma Types.Forall Cubical.DPath.

(** * Quotient of a graph *)

(** ** Definition *)

(** The quotient of a graph is one of the simplest HITs that can be found in HoTT. It consists of a base type and a relation on it, and for every witness of a relation between two points of the type, a path.

We use graph quotients to build up all our other non-recursive HITs. Their simplicity means that we can easily prove results about them and generalise them to other HITs. *)

Local Unset Elimination Schemes.

Module Export GraphQuotient.

  Private Inductive GraphQuotient@{i j u}
    {A : Type@{i}} (R : A -> A -> Type@{j}) : Type@{u} :=
  | gq : A -> GraphQuotient R.

  Arguments gq {A R} a.

  Axiom gqglue@{i j u}
    : forall {A : Type@{i}} {R : A -> A -> Type@{j}} {a b : A},
    R a b -> paths@{u} (@gq A R a) (gq b).

  Definition GraphQuotient_ind@{i j u k} {A : Type@{i}} {R : A -> A -> Type@{j}}
    (P : GraphQuotient@{i j u} R -> Type@{k})
    (gq' : forall a, P (gq@{i j u} a))
    (gqglue' : forall a b (s : R a b), gqglue@{i j u} s # gq' a = gq' b)
    : forall x, P x := fun x =>
    match x with
    | gq a => fun _ => gq' a
    end gqglue'.
  (** Above we did a match with output type a function, and then outside of the match we provided the argument [gqglue'].  If we instead end with [| gq a => gq' a end.], the definition will not depend on [gqglue'], which would be incorrect.  This is the idiom referred to in ../../test/bugs/github1758.v and github1759.v. *)

  Axiom GraphQuotient_ind_beta_gqglue@{i j u k}
  : forall  {A : Type@{i}} {R : A -> A -> Type@{j}}
    (P : GraphQuotient@{i j u} R -> Type@{k})
    (gq' : forall a, P (gq a))
    (gqglue' : forall a b (s : R a b), gqglue s # gq' a = gq' b)
    (a b: A) (s : R a b),
    apD (GraphQuotient_ind P gq' gqglue') (gqglue s) = gqglue' a b s.

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

(** ** Flattening lemma *)

(** The flattening lemma, also known as descent, is a fundamental result in higher topos theory. Stated in it's simplest form, it says that limits (sigma types) commute with colimits (graph quotients) in an appropriate way. This is a particularly far reaching result in homotopy theory and will prove very useful later on.

HITs on their own do not have these properties, but by using the univalence axiom, we can prove properties about HITs that were not available before. In some ways, descent is what characterizes a higher topos to begin with, so it is nice to see univalence directly giving this property. In that way, univalence can be thought of the thing that makes a higher topos tick. *) 

Section Flattening.
  
  (** In order to state the main lemma we will need to make some common assumptions which we will do in this section. *)

  Context
    (** As mentioned before, univalence will play a crucial role in the definition of the flattening lemma. *)
    `{Univalence}
    (** We start with a type [A] and a binary relation [R] on that type. *)
    {A : Type} {R : A -> A -> Type}
    (** Next we consider a type family over this base type which is further more "equifibrant". This means that each of the fibers of this family are equivalent as types as long as the base poitns are related by [R]. *)
    (F : A -> Type) (e : forall x y, R x y -> F x <~> F y).

  (** Now we can define a family over [GraphQuotient R], clearly representatives of the equivalence classes can be mapped using the family [F], in order to make sure that this is well defined we need to know that any two fibers of related points are equal. This is where univalence comes in as it allows us to promote our equivalence to an identity. *)
  Definition DGraphQuotient : GraphQuotient R -> Type
    := GraphQuotient_rec F (fun x y r => path_universe (e x y r)).

  (** When transporting [DGraphQuotient] along [gqglue] we can compute this as the equivalence [e] applied to the original point. This lemma is required a few times in the following proofs. *)
  Definition transport_DGraphQuotient {x y} (s : R x y) (a : F x)
    : transport DGraphQuotient (gqglue s) a = e x y s a.
  Proof.
    lhs nrapply transport_idmap_ap.
    lhs nrapply (transport2 idmap).
    1: apply GraphQuotient_rec_beta_gqglue.
    rapply transport_path_universe.
  Defined.

  (** The family [DGraphQuotient] we have defined over [GraphQuotient R] has a total space which we will aim to describe. Notably, this total space acts just like a [GraphQuotient] of [sig F] by an appropriate relation. *)

  (** We can mimic the constructors of [GraphQuotient] for the total space. Here is the point constructor. *)
  Definition flatten_gq {x} : F x -> sig DGraphQuotient.
  Proof.
    intros p.
    exists (gq x).
    assumption.
  Defined.
  
  (** And here is the path constructor. *)
  Definition flatten_gqglue {x y} (r : R x y) (a : F x)
    : flatten_gq a = flatten_gq (e x y r a).
  Proof.
    snrapply path_sigma'.
    - by apply gqglue.
    - apply transport_DGraphQuotient.
  Defined.

  (** This lemma is the same as [transport_DGraphQuotient] but adapted instead for [DPath]. The use of [DPath] will be apparent there. *)
  Lemma equiv_dp_dgraphquotient (x y : A) (s : R x y) (a : F x) (b : F y)
    : DPath DGraphQuotient (gqglue s) a b <~> e x y s a = b.
  Proof.
    refine (_ oE dp_path_transport^-1).
    refine (equiv_concat_l _^ _).
    apply transport_DGraphQuotient.
  Defined.

  (** We can also prove an induction principle for [sig DGraphQuotient]. We won't show that it satisfies the relevant computation rules, but these will not be needed. Instead we will prove the non-dependent eliminator directly so that we can better reason about it. Another thing to note, in order to get through the path algebra here, we have opted to use dependent paths. This makes the reasoning steps slightly easier, but it should not matter too much. *)
  Definition flatten_ind {Q : sig DGraphQuotient -> Type}
    (Qgq : forall a (x : F a), Q (flatten_gq x))
    (Qgqglue : forall a b (r : R a b) (x : F a),
      flatten_gqglue r x # Qgq _ x = Qgq _ (e _ _ _ x))
    : forall x, Q x.
  Proof.
    apply sig_ind.
    snrapply GraphQuotient_ind.
    1: exact Qgq.
    intros a b s.
    apply equiv_dp_path_transport.
    apply dp_forall.
    intros x y.
    srapply (equiv_ind (equiv_dp_dgraphquotient a b s x y)^-1).
    intros q.
    destruct q.
    apply equiv_dp_path_transport.
    refine (transport2 _ _ _ @ Qgqglue a b s x).
    refine (ap (path_sigma_uncurried DGraphQuotient _ _) _).
    snrapply path_sigma.
    1: reflexivity.
    apply moveR_equiv_V.
    simpl; f_ap.
    lhs rapply concat_p1.
    rapply inv_V.
  Defined.

  (** Rather than use [flatten_ind] to define [flatten_rec] we reprove this simple case. This means we can later reason about it and derive the computation rules easily. The full computation rule for [flatten_ind] takes some work to derive and is not actually needed. *)
  Definition flatten_rec {Q : Type} (Qgq : forall a, F a -> Q)
    (Qgqglue : forall a b (r : R a b) (x : F a), Qgq a x = Qgq b (e _ _ r x))
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
    lhs nrapply ap_sig_rec_path_sigma.
    rewrite GraphQuotient_ind_beta_gqglue.
    simpl.
    apply moveR_pM.
    apply moveL_pM.
    rewrite 3 concat_pp_p.
    apply moveR_Vp.
    rewrite (ap10_dpath_arrow DGraphQuotient (fun _ => Q) (gqglue s)).
    hott_simpl.
    rewrite concat_pp_p.
    apply moveR_Mp.
    rewrite concat_Vp.
    apply moveR_pM.
    rewrite concat_1p.
    rapply ap_V.
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
      rewrite flatten_rec_beta_gqglue.
      rewrite concat_p1.
      apply concat_Vp.
    - snrapply flatten_ind.
      1: reflexivity.
      intros a b r x.
      lhs nrapply (transport_paths_FFlr (g := GraphQuotient_rec _ _) _).
      rewrite flatten_rec_beta_gqglue.
      rewrite GraphQuotient_rec_beta_gqglue.
      rewrite concat_p1.
      apply concat_Vp.
  Defined.

End Flattening.
