From HoTT.Basics Require Import Overture Equivalences Tactics.
From HoTT.WildCat Require Import Core Equiv ZeroGroupoid EquivGpd
                                 NatTrans Opposite Yoneda FunctorCat.

(** * Categories with equalizers *)

(** When [eq] is the source object in a double arrow diagram, then for any object [z] we get a commuting diagram of 0-groupoids by applying the functor [z $-> -], which is [opyon_0gpd z].  Thus there is a natural map of 0-groupoids from [z $-> pb] to the 0-groupoid equalizer of

<<
                  -->
        (z $-> a)     (z $-> b)
                  -->
>>
In this diagram, the hom sets are regarded as 0-groupoids and the top-level arrows are morphisms of 0-groupoids (0-functors).*)

Definition cat_eq_corec_inv {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  (eq : A) (inj : eq $-> a) (glue : f $o inj $== g $o inj)
  (z : A)
  : opyon_0gpd z eq $-> equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g).
Proof.
  snapply equiv_equalizer_0gpd_corec.
  exists (fmap _ inj).
  refine ((fmap_comp _ inj f)^$ $@ _ $@ fmap_comp _ inj g).
  exact (fmap2 _ glue).
Defined.

(** An equalizer is an object completing [f] and [g] to a commuting diagram such that the map above is an equivalence of 0-groupoids for each [z]. *)
Class IsCatEqualizer {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b) (cat_eq : A)
  := Build_IsCatEqualizer' {
    cat_eq_inj : cat_eq $-> a;
    cat_eq_glue : f $o cat_eq_inj $== g $o cat_eq_inj;
    catie_cat_eq_corec_inv
      :: forall z : A, CatIsEquiv (cat_eq_corec_inv f g
                                cat_eq cat_eq_inj cat_eq_glue z);
  }.

Arguments Build_IsCatEqualizer' {A IsGraph Is2Graph Is01Cat H a b}
  f g cat_eq cat_eq_inj cat_eq_glue eq : rename.

Class CatEqualizer {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
  := Build_CatEqualizer' {
    cat_eq : A;
    cat_iseq :: IsCatEqualizer f g cat_eq;
  }.

Arguments Build_CatEqualizer' {A IsGraph Is2Graph Is01Cat H a b}
  f g : rename.
Arguments cat_eq {A IsGraph Is2Graph Is01Cat H a b} f g {eq} : rename.

Section EqualizerConstructors.

  Context {A : Type} `{Is1Cat A} {a b : A} (f g : a $-> b)
    (cat_eq : A) (cat_eq_inj : cat_eq $-> a)
    (cat_eq_glue : f $o cat_eq_inj $== g $o cat_eq_inj)
    (cat_eq_corec : forall z : A,
      equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g) -> (z $-> cat_eq))
    (cat_eq_beta_inj : forall z hp, cat_eq_inj $o cat_eq_corec z hp $-> hp.1)
    (cat_eq_eta : forall z (k h : z $-> cat_eq)
      (p : cat_eq_inj $o k $== cat_eq_inj $o h), k $== h).

  (** A convenience wrapper for building [IsCatEqualizer]. *)
  Definition Build_IsCatEqualizer : IsCatEqualizer f g cat_eq.
  Proof.
    snapply (Build_IsCatEqualizer' f g cat_eq cat_eq_inj cat_eq_glue).
    intros z.
    napply isequiv_0gpd_issurjinj.
    napply Build_IsSurjInj.
    - intros hp.
      exists (cat_eq_corec z hp).
      exact (cat_eq_beta_inj z hp).
    - intros k h p.
      exact (cat_eq_eta z k h p).
  Defined.

  (** A convenience wrapper for building equalizers. *)
  Definition Build_CatEqualizer : CatEqualizer f g
    := Build_CatEqualizer' f g cat_eq Build_IsCatEqualizer.

End EqualizerConstructors.

Section Lemmata.

  Context {A : Type} `{Is1Cat A}
    {a b : A} (f g : a $-> b)
    {cat_eq : A}
    `{!IsCatEqualizer f g cat_eq}
    (z : A).

  Definition cate_eq_corec_inv : opyon_0gpd z cat_eq $<~>
        equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)
    := Build_CatEquiv _.

  Definition cate_eq_corec
    : equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)
      $<~> opyon_0gpd z cat_eq
  := cate_eq_corec_inv^-1$.

  Definition cat_eq_corec
    (h : z $-> a) (p : f $o h $== g $o h)
    : z $-> cat_eq.
  Proof.
    apply cate_eq_corec.
    simpl.
    exact (h; p).
  Defined.

  Definition cat_eq_corec_beta_inj
    (h : z $-> a) (p : f $o h $== g $o h)
    : cat_eq_inj $o cat_eq_corec h p $== h
    := cate_isretr cate_eq_corec_inv _.

  Definition cat_eq_inj_postcomp_glue (h : z $-> cat_eq)
    := (cat_assoc _ _ _)^$ $@ (cat_eq_glue $@R h) $@ cat_assoc _ _ _.

  Definition cat_eq_corec_eta_inj (h : z $-> cat_eq)
    : cat_eq_corec (cat_eq_inj $o h) (cat_eq_inj_postcomp_glue h) $== h
    := cate_issect cate_eq_corec_inv h.

  Definition cat_eq_corec_eta (h h' : z $-> a)
    (glue_h : f $o h $== g $o h) (glue_h' : f $o h' $== g $o h')
    (p : h $== h')
    : cat_eq_corec h glue_h $== cat_eq_corec h' glue_h'.
  Proof.
    apply (isinj_equiv_0gpd cate_eq_corec_inv).
    cbn.
    lhs' apply (cat_eq_corec_beta_inj h glue_h).
    lhs' apply p.
    exact (cat_eq_corec_beta_inj h' glue_h')^$.
  Defined.

End Lemmata.

Local Instance is0functor_equalizer_0gpd_helper {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  : Is0Functor (A:=A^op)
    (fun z : A => equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  napply Build_Is0Functor.
  intros z1 z2 k; unfold op in *.
  snapply Build_Fun01'.
  - intros [h p].
    exists (h $o k).
    exact ((cat_assoc _ _ _)^$ $@ (p $@R k) $@ cat_assoc _ _ _).
  - intros [h1 p1] [h2 p2] q.
    exact (q $@R k).
Defined.

Local Instance is1functor_equalizer_0gpd_helper {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b)
  : Is1Functor (A:=A^op)
    (fun z : A => equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  napply Build_Is1Functor.
  - intros z1 z2 k1 k2 p [h glue_h].
    exact (h $@L p).
  - intros z [h glue_h].
    exact (cat_idr h).
  - intros z1 z2 z3 k1 k2 [h glue_h].
    napply cat_assoc_opp; exact _.
Defined.

Definition natequiv_cat_eq_corec_inv {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b) (cat_eq : A) `{!IsCatEqualizer f g cat_eq}
  : NatEquiv (A:=A^op) (yon_0gpd cat_eq)
    (fun z : A => equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g)).
Proof.
  snapply Build_NatEquiv.
  - exact (cate_eq_corec_inv f g).
  - exact (is1natural_yoneda_0gpd cat_eq
    (fun z : A => equalizer_0gpd (fmap (opyon_0gpd z) f) (fmap (opyon_0gpd z) g))
    (cat_eq_inj; cat_eq_glue)).
Defined.

(** ** Uniqueness of equalizers *)

Definition cat_eq_unique {A : Type} `{HasEquivs A}
  {a b : A} (f g : a $-> b)
  (eq1 : A) `{!IsCatEqualizer f g eq1}
  (eq2 : A) `{!IsCatEqualizer f g eq2}
  : eq1 $<~> eq2.
Proof.
  napply yon_equiv_0gpd.
  refine (natequiv_compose _ (natequiv_cat_eq_corec_inv f g eq1)).
  exact (natequiv_inverse (natequiv_cat_eq_corec_inv f g eq2)).
Defined.

(** ** Induced Equalizers *)

Section InducedFromEquiv.

  Context {A : Type} `{he : HasEquivs A} {a b : A} {f g : a $-> b}
    (cat_eq : A) `{!IsCatEqualizer f g cat_eq}
    (y : A) (h : y $<~> cat_eq).

  (** A categorical equivalence into an equalizer induces an equalizer structure on the domain. *)
  Local Instance cat_eq_equiv_eq : IsCatEqualizer f g y.
  Proof.
    snapply Build_IsCatEqualizer.
    - exact (cat_eq_inj $o h).
    - exact (cat_eq_inj_postcomp_glue f g _ h).
    - intros z [k p].
      exact (h^-1$ $o cat_eq_corec f g z k p).
    - intros z [k p]; cbn beta.
      refine (_ $@ cat_eq_corec_beta_inj f g z k p).
      refine (cat_assoc _ _ _ $@ _).
      apply cat_postwhisker.
      apply compose_h_Vh.
    - cbn beta; intros z k k' e.
      napply (cate_monic_equiv h).
      apply (isinj_equiv_0gpd (cate_eq_corec_inv f g z)).
      exact (cat_assoc_opp _ _ _ $@ e $@ cat_assoc _ _ _).
  Defined.

  (** The induced injection is given by the equivalence. *)
  Definition cat_eq_inj_comp
    : cat_eq_inj $== cat_eq_inj $o h
    := Id _.

  (** The induced corecursion is given by the equivalence. *)
  Definition cat_eq_corec_comp {z : A} (k : z $-> a) (p : f $o k $== g $o k)
    : h $o cat_eq_corec (IsCatEqualizer0:=cat_eq_equiv_eq) f g z k p $== cat_eq_corec f g z k p
    := compose_h_Vh _ _.

End InducedFromEquiv.

(** ** Symmetry *)

Section Symmetry.

  Context {A : Type} `{Is1Cat A} {a b : A} {f g : a $-> b}
    (cat_eq : A) `{!IsCatEqualizer f g cat_eq}.

  (** An equalizer of [f] and [g] is also an equalizer of [g] and [f]. *)
  Definition iscatequalizer_sym : IsCatEqualizer g f cat_eq.
  Proof.
    snapply Build_IsCatEqualizer.
    - exact cat_eq_inj.
    - exact cat_eq_glue^$.
    - intros z [k p].
      exact (cat_eq_corec f g z k p^$).
    - intros z [k p]; cbn beta.
      exact (cat_eq_corec_beta_inj f g z k p^$).
    - intros z k k' e.
      exact (isinj_equiv_0gpd (cate_eq_corec_inv f g z) e).
  Defined.

End Symmetry.

(** ** Categories with equalizers *)

Class HasEqualizers (A : Type) `{Is1Cat A}
  := has_equalizers :: forall {a b} (f g : a $-> b), CatEqualizer f g.

(** ** Examples *)

(** *** Equalizers in ZeroGpd *)

Instance has_equalizers_0gpd : HasEqualizers ZeroGpd.
Proof.
  intros G H f g.
  snapply (Build_CatEqualizer f g (equalizer_0gpd f g)
             (equalizer_0gpd_inj f g) (equalizer_0gpd_eq f g)).
  - intros Z hp.
    exact (equiv_equalizer_0gpd_corec f g hp).
  - reflexivity.
  - exact (equalizer_0gpd_homotopic f g).
Defined.


(** * Monics *)

(** The equalizer map is a monomorphism. *)

Local Instance monic_cat_equalizer {A : Type} `{Is1Cat A}
  {a b : A} (f g : a $-> b) {cat_eq : A} `{!IsCatEqualizer f g cat_eq}
  : Monic cat_eq_inj.
Proof.
  intros ? ? ? p.
  exact (isinj_equiv_0gpd (cate_eq_corec_inv _ _ _) p).
Defined.

(** Equalizers define a subclass of strong monomorphisms, namely monos which have the right lifting property against epis. *)

(** TODO: move everything about strong monics to a different file? *)

Class StrongMonic {A : Type} `{Is1Cat A} {a b : A} (m : a $-> b) := {
  ismonic_strongmonic :: Monic m;
  rlp_strongmonic {a' b'} (e : a' $->> b') (u : a' $-> a) (v : b' $-> b)
    (sq : v $o e $== m $o u) : b' $-> a;
  rlp_lcomm_strongmonic {a' b'} (e : a' $->> b') (u : a' $-> a) (v : b' $-> b)
    (sq : v $o e $== m $o u) : m $o rlp_strongmonic e u v sq $== v
}.

Definition rlp_ucomm_strongmonic {A : Type} `{Is1Cat A} {a b : A} (m : a $-> b) `{!StrongMonic m}
  {a' b'} (e : a' $->> b') (u : a' $-> a) (v : b' $-> b) (sq : v $o e $== m $o u)
  : rlp_strongmonic e u v sq $o e $== u.
Proof.
  rapply (ismonic m).
  lhs' napply cat_assoc_opp.
  lhs' napply (rlp_lcomm_strongmonic e u v sq $@R e).
  exact sq.
Defined.

Definition rlp_unique_strongmonic {A : Type} `{Is1Cat A} {a b : A} (m : a $-> b) `{!StrongMonic m}
  {a' b'} (e : a' $->> b') (u : a' $-> a) (v : b' $-> b) (sq : v $o e $== m $o u)
  (h : b' $-> a) (ltr : m $o h $== v)
  : rlp_strongmonic e u v sq $== h.
Proof.
  rapply (ismonic m).
  lhs' napply rlp_lcomm_strongmonic.
  exact ltr^$.
Defined.

(** The map [cat_eq_inj] is a strong monic. *)
Local Instance strongmonic_equalizer {A : Type} `{Is1Cat A} {b c : A}
  (f g : b $-> c) {cat_eq : A} `{!IsCatEqualizer f g cat_eq}
  : StrongMonic cat_eq_inj.
Proof.
  set (m := cat_eq_inj).
  srapply Build_StrongMonic.
  - intros a' b' e u v sq.
    apply (cat_eq_corec f g _ v).
    apply (isepic e).
    lhs' napply cat_assoc; rhs' napply cat_assoc.
    lhs' napply (f $@L sq); rhs' napply (g $@L sq).
    lhs' napply cat_assoc_opp; rhs' napply cat_assoc_opp.
    rapply cat_prewhisker.
    exact cat_eq_glue.
  - intros a' b' e u v sq; cbn.
    napply cat_eq_corec_beta_inj.
Defined.
