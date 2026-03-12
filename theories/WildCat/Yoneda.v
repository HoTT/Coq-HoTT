Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Universe.
Require Import WildCat.Opposite.
Require Import WildCat.FunctorCat.
Require Import WildCat.NatTrans.
Require Import WildCat.Prod.
Require Import WildCat.Bifunctor.
Require Import WildCat.ZeroGroupoid.

(** ** Two-variable hom-functors *)

Instance is0functor_hom {A} `{Is01Cat A}
  : @Is0Functor (A^op * A) Type _ _ (uncurry (@Hom A _)).
Proof.
  apply Build_Is0Functor.
  intros [a1 a2] [b1 b2] [f1 f2] g; cbn in *.
  exact (f2 $o g $o f1).
Defined.

(** This requires morphism extensionality! *)
Instance is1functor_hom {A} `{HasMorExt A}
  : @Is1Functor (A^op * A) Type _ _ _ _ _ _ _ _ (uncurry (@Hom A _)) _.
Proof.
  apply Build_Is1Functor.
  - intros [a1 a2] [b1 b2] [f1 f2] [g1 g2] [p1 p2] q;
      unfold fst, snd in *.
    apply path_hom.
    exact (((p2 $@R q) $@R _) $@ ((g2 $o q) $@L p1)).
  - intros [a1 a2] f; cbn in *.
    apply path_hom.
    exact (cat_idr _ $@ cat_idl f).
  - intros [a1 a2] [b1 b2] [c1 c2] [f1 f2] [g1 g2] h; cbn in *.
    apply path_hom.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine (_ $@ cat_assoc_opp _ _ _).
    refine (g2 $@L _).
    refine (_ $@ cat_assoc_opp _ _ _).
    exact (cat_assoc_opp _ _ _).
Defined.

Instance is0bifunctor_hom {A} `{Is01Cat A}
  : Is0Bifunctor (A:=A^op) (B:=A) (C:=Type) (@Hom A _).
Proof.
  napply Build_Is0Bifunctor'.
  1-2: exact _.
  exact is0functor_hom.
Defined.

(** While it is possible to prove the bifunctor coherence condition from [Is1Cat_Strong], 1-functoriality requires morphism extensionality.*)
Instance is1bifunctor_hom {A} `{Is1Cat A} `{HasMorExt A}
  : Is1Bifunctor (A:=A^op) (B:=A) (C:=Type) (@Hom A _).
Proof.
  napply Build_Is1Bifunctor'.
  exact is1functor_hom.
Defined.

Definition fun01_hom {A} `{Is01Cat A}
  : Fun01 (A^op * A) Type
  := @Build_Fun01 _ _ _ _ _ is0functor_hom.

(** ** The covariant Yoneda lemma *)

(** This is easier than the contravariant version because it doesn't involve any "op"s. *)

Definition opyon {A : Type} `{IsGraph A} (a : A) : A -> Type
  := fun b => (a $-> b).

(** We prove this explicitly instead of using the bifunctor instance above so that we can apply [fmap] in each argument independently without mapping an identity in the other. *)
Instance is0functor_opyon {A : Type} `{Is01Cat A} (a : A)
  : Is0Functor (opyon a).
Proof.
  apply Build_Is0Functor.
  unfold opyon; intros b c f g; cbn in *.
  exact (f $o g).
Defined.

Instance is1functor_opyon {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A)
  : Is1Functor (opyon a).
Proof.
  rapply Build_Is1Functor.
  + intros x y f g p h.
    apply path_hom.
    apply (cat_prewhisker p).
  + intros x h.
    apply path_hom.
    apply cat_idl.
  + intros x y z f g h.
    apply path_hom.
    apply cat_assoc.
Defined.

(** We record these corollaries here, since we use some of them below. *)
Definition equiv_postcompose_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt A}
  {x y z : A} (f : y $<~> z)
  : (x $-> y) <~> (x $-> z)
  := emap (opyon x) f.

Definition equiv_precompose_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt A}
  {x y z : A} (f : x $<~> y)
  : (y $-> z) <~> (x $-> z)
  := @equiv_postcompose_cat_equiv A^op _ _ _ _ _ _ z y x f.

(* The following implicitly use [hasequivs_core].  Note that when [A] has morphism extensionality, it doesn't follow that [core A] does.  We'd need to know that being an equivalence is a proposition, and we don't assume that (since even for [Type] it requires [Funext], see [hasmorext_core_type]). So we need to assume this in the following results. *)

(** Postcomposition with a cat_equiv is an equivalence between the types of equivalences. *)
Definition equiv_postcompose_core_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt (core A)}
  {x y z : A} (f : y $<~> z)
  : (x $<~> y) <~> (x $<~> z).
Proof.
  change ((Build_core x $-> Build_core y) <~> (Build_core x $-> Build_core z)).
  refine (equiv_postcompose_cat_equiv (A := core A) _).
  exact f.  (* It doesn't work to insert [f] on the previous line. *)
Defined.

Definition equiv_precompose_core_cat_equiv {A : Type} `{HasEquivs A} `{!HasMorExt (core A)}
  {x y z : A} (f : x $<~> y)
  : (y $<~> z) <~> (x $<~> z).
Proof.
  change ((Build_core y $-> Build_core z) <~> (Build_core x $-> Build_core z)).
  refine (equiv_precompose_cat_equiv (A := core A) _).
  exact f.  (* It doesn't work to insert [f] on the previous line. *)
Defined.

Definition opyoneda {A : Type} `{Is01Cat A} (a : A)
           (F : A -> Type) {ff : Is0Functor F}
  : F a -> (opyon a $=> F).
Proof.
  intros x b f.
  exact (fmap F f x).
Defined.

Definition un_opyoneda {A : Type} `{Is01Cat A}
  (a : A) (F : A -> Type) {ff : Is0Functor F}
  : (opyon a $=> F) -> F a
  := fun alpha => alpha a (Id a).

Instance is1natural_opyoneda {A : Type} `{Is1Cat A}
  (a : A) (F : A -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (opyon a) F (opyoneda a F x).
Proof.
  snapply Build_Is1Natural.
  unfold opyon, opyoneda; intros b c f g; cbn in *.
  exact (fmap_comp F g f x).
Defined.

(** This is form of injectivity of [opyoneda]. *)
Definition opyoneda_isinj {A : Type} `{Is1Cat A} (a : A)
  (F : A -> Type) `{!Is0Functor F, !Is1Functor F}
  (x x' : F a) (p : forall b, opyoneda a F x b == opyoneda a F x' b)
  : x = x'.
Proof.
  refine ((fmap_id F a x)^ @ _ @ fmap_id F a x').
  cbn in p.
  exact (p a (Id a)).
Defined.

(** This says that [opyon] is faithful, although we haven't yet defined a graph structure on natural transformations to express this in that way.  This follows from the previous result, but then would need [HasMorExt A], since the previous result assumes that [F] is a 1-functor, which is stronger than what is needed.  The direct proof below only needs the weaker assumption [Is1Cat_Strong A]. *)
Definition opyon_faithful {A : Type} `{Is1Cat_Strong A}
  (a b : A) (f g : b $-> a)
  (p : forall (c : A) (h : a $-> c), h $o f = h $o g)
  : f = g
  := (cat_idl_strong f)^ @ p a (Id a) @ cat_idl_strong g.

(** The composite in one direction is the identity map. *)
Definition opyoneda_issect {A : Type} `{Is1Cat A} (a : A)
           (F : A -> Type) `{!Is0Functor F, !Is1Functor F}
           (x : F a)
  : un_opyoneda a F (opyoneda a F x) = x
  := fmap_id F a x.

(** We assume for the converse that the coherences in [A] are equalities (this is a weak funext-type assumption).  Note that we do not in general recover the witness of 1-naturality.  Indeed, if [A] is fully coherent, then a transformation of the form [opyoneda a F x] is always also fully coherently natural, so an incoherent witness of 1-naturality could not be recovered in this way.  *)
Definition opyoneda_isretr {A : Type} `{Is1Cat_Strong A} (a : A)
           (F : A -> Type) `{!Is0Functor F, !Is1Functor F}
           (alpha : opyon a $=> F) {alnat : Is1Natural (opyon a) F alpha}
           (b : A)
  : opyoneda a F (un_opyoneda a F alpha) b $== alpha b.
Proof.
  unfold opyoneda, un_opyoneda, opyon; intros f.
  refine ((isnat alpha f (Id a))^ @ _).
  cbn.
  apply ap.
  exact (cat_idr_strong f).
Defined.

(** A natural transformation between representable functors induces a map between the representing objects. *)
Definition opyon_cancel {A : Type} `{Is01Cat A} (a b : A)
  : (opyon a $=> opyon b) -> (b $-> a)
  := un_opyoneda a (opyon b).

Definition opyon1 {A : Type} `{Is01Cat A} (a : A) : Fun01 A Type.
Proof.
  exact (Build_Fun01 (opyon a)).
Defined.

Definition opyon11 {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A) : Fun11 A Type.
Proof.
  exact (Build_Fun11 _ _ (opyon a)).
Defined.

(** An equivalence between representable functors induces an equivalence between the representing objects. *)
Definition opyon_equiv {A : Type} `{HasEquivs A} `{!Is1Cat_Strong A}
           {a b : A}
  : (opyon1 a $<~> opyon1 b) -> (b $<~> a).
Proof.
  intros f.
  refine (cate_adjointify (f a (Id a)) (f^-1$ b (Id b)) _ _);
    apply GpdHom_path; cbn in *.
  - refine ((isnat_natequiv (natequiv_inverse f) (f a (Id a)) (Id b))^ @ _); cbn.
    refine (_ @ cate_issect (f a) (Id a)); cbn.
    apply ap.
    srapply cat_idr_strong.
  - refine ((isnat_natequiv f (f^-1$ b (Id b)) (Id a))^ @ _); cbn.
    refine (_ @ cate_isretr (f b) (Id b)); cbn.
    apply ap.
    srapply cat_idr_strong.
Defined.

Definition natequiv_opyon_equiv {A : Type} `{HasEquivs A}
  `{!HasMorExt A} {a b : A}
  : (b $<~> a) -> (opyon1 a $<~> opyon1 b).
Proof.
  intro e.
  snapply Build_NatEquiv.
  - intros c.
    exact (equiv_precompose_cat_equiv e).
  - rapply is1natural_opyoneda.
Defined.

(** ** The covariant Yoneda lemma using 0-groupoids *)

(** We repeat the above, regarding [opyon] as landing in 0-groupoids, using the 1-category structure on [ZeroGpd] in [ZeroGroupoid.v].  This has many advantages.  It avoids [HasMorExt], which means that we don't need [Funext] in many examples.  It also avoids [Is1Cat_Strong], which means the results all have the same hypotheses, namely that [A] is a 1-category.  This allows us to simplify the proof of [opyon_equiv_0gpd], making use of [opyoneda_isretr_0gpd]. *)

Definition opyon_0gpd {A : Type} `{Is1Cat A} (a : A) : A -> ZeroGpd
  := fun b => Build_ZeroGpd (a $-> b) _ _ _.

Instance is0functor_hom_0gpd {A : Type} `{Is1Cat A}
  : Is0Functor (A:=A^op*A) (B:=ZeroGpd) (uncurry (opyon_0gpd (A:=A))).
Proof.
  napply Build_Is0Functor.
  intros [a1 a2] [b1 b2] [f1 f2]; unfold op in *; cbn in *.
  rapply (Build_Fun01 (cat_postcomp b1 f2 o cat_precomp a2 f1)).
Defined.

Instance is1functor_hom_0gpd {A : Type} `{Is1Cat A}
  : Is1Functor (A:=A^op*A) (B:=ZeroGpd) (uncurry (opyon_0gpd (A:=A))).
Proof.
  napply Build_Is1Functor.
  - intros [a1 a2] [b1 b2] [f1 f2] [g1 g2] [p q] h.
    exact (h $@L p $@@ q).
  - intros [a1 a2] h.
    exact (cat_idl _ $@ cat_idr _).
  - intros [a1 a2] [b1 b2] [c1 c2] [f1 f2] [g1 g2] h.
    refine (cat_assoc _ _ _ $@ _).
    refine (g2 $@L _).
    refine (_ $@L (cat_assoc_opp _ _ _) $@ _).
    exact (cat_assoc_opp _ _ _).
Defined.

Instance is0bifunctor_hom_0gpd {A : Type} `{Is1Cat A}
  : Is0Bifunctor (A:=A^op) (B:=A) (C:=ZeroGpd) (opyon_0gpd (A:=A)).
Proof.
  snapply Build_Is0Bifunctor'.
  1,2: exact _.
  exact is0functor_hom_0gpd.
Defined.

Instance is1bifunctor_hom_0gpd {A : Type} `{Is1Cat A}
  : Is1Bifunctor (A:=A^op) (B:=A) (C:=ZeroGpd) (opyon_0gpd (A:=A)).
Proof.
  snapply Build_Is1Bifunctor'.
  exact is1functor_hom_0gpd.
Defined.

Instance is0functor_opyon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is0Functor (opyon_0gpd a).
Proof.
  apply Build_Is0Functor.
  intros b c f.
  exact (Build_Fun01 (cat_postcomp a f)).
Defined.

Instance is1functor_opyon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is1Functor (opyon_0gpd a).
Proof.
  rapply Build_Is1Functor.
  + intros x y f g p h.
    apply (cat_prewhisker p).
  + intros x h.
    apply cat_idl.
  + intros x y z f g h.
    apply cat_assoc.
Defined.

Definition opyoneda_0gpd {A : Type} `{Is1Cat A} (a : A)
           (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  : F a -> (opyon_0gpd a $=> F).
Proof.
  intros x b.
  refine (Build_Fun01' (A:=opyon_0gpd a b) (B:=F b) (fun f => fmap F f x) _).
  intros f1 f2 h.
  exact (fmap2 F h x).
Defined.

Definition un_opyoneda_0gpd {A : Type} `{Is1Cat A}
  (a : A) (F : A -> ZeroGpd) {ff : Is0Functor F}
  : (opyon_0gpd a $=> F) -> F a
  := fun alpha => alpha a (Id a).

Instance is1natural_opyoneda_0gpd {A : Type} `{Is1Cat A}
  (a : A) (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (opyon_0gpd a) F (opyoneda_0gpd a F x).
Proof.
  snapply Build_Is1Natural.
  unfold opyon_0gpd, opyoneda_0gpd; intros b c f g; cbn in *.
  exact (fmap_comp F g f x).
Defined.

(** This is form of injectivity of [opyoneda_0gpd]. *)
Definition opyoneda_isinj_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (x x' : F a) (p : forall b : A, opyoneda_0gpd a F x b $== opyoneda_0gpd a F x' b)
  : x $== x'.
Proof.
  refine ((fmap_id F a x)^$ $@ _ $@ fmap_id F a x').
  cbn in p.
  exact (p a (Id a)).
Defined.

(** This says that [opyon_0gpd] is faithful, although we haven't yet defined a graph structure on natural transformations to express this in that way. *)
Definition opyon_faithful_0gpd {A : Type} `{Is1Cat A} (a b : A)
  (f g : b $-> a) (p : forall (c : A) (h : a $-> c), h $o f $== h $o g)
  : f $== g
  := opyoneda_isinj_0gpd a _ f g p.

(** The composite in one direction is the identity map. *)
Definition opyoneda_issect_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (x : F a)
  : un_opyoneda_0gpd a F (opyoneda_0gpd a F x) $== x
  := fmap_id F a x.

(** For the other composite, note that we do not in general recover the witness of 1-naturality.  Indeed, if [A] is fully coherent, then a transformation of the form [opyoneda a F x] is always also fully coherently natural, so an incoherent witness of 1-naturality could not be recovered in this way.  *)
Definition opyoneda_isretr_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (alpha : opyon_0gpd a $=> F) {alnat : Is1Natural (opyon_0gpd a) F alpha}
  (b : A)
  : opyoneda_0gpd a F (un_opyoneda_0gpd a F alpha) b $== alpha b.
Proof.
  unfold opyoneda, un_opyoneda, opyon; intros f.
  refine ((isnat alpha f (Id a))^$ $@ _).
  cbn.
  apply (fmap (alpha b)).
  exact (cat_idr f).
Defined.

(** A natural transformation between representable functors induces a map between the representing objects. *)
Definition opyon_cancel_0gpd {A : Type} `{Is1Cat A} (a b : A)
  : (opyon_0gpd a $=> opyon_0gpd b) -> (b $-> a)
  := un_opyoneda_0gpd a (opyon_0gpd b).

(** Since no extra hypotheses are needed, we use the name with "1" for the [Fun11] version. *)
Definition opyon1_0gpd {A : Type} `{Is1Cat A} (a : A) : Fun11 A ZeroGpd
  := Build_Fun11 _ _ (opyon_0gpd a).

(** An equivalence between representable functors induces an equivalence between the representing objects.  We explain how this compares to [opyon_equiv] above.  Instead of assuming that each [f c : (a $-> c) -> (b $-> c)] is an equivalence of types, it only needs to be an equivalence of 0-groupoids.  For example, this means that we have a map [g c : (b $-> c) -> (a $-> c)] such that for each [k : a $-> c], [g c (f c k) $== k], rather than [g c (f c k) = k] as the version with types requires.  Similarly, the naturality is up to 2-cells, instead of up to paths.  This allows us to avoid [Funext] and [HasMorExt] when using this result.  As a side benefit, we also don't require that [A] is strong. The proof is also simpler, since we can re-use the work done in [opyoneda_isretr_0gpd]. *)
Definition opyon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (f : opyon1_0gpd a $<~> opyon1_0gpd b)
  : b $<~> a.
Proof.
  (* These are the maps that will define the desired equivalence: *)
  set (fa := (cate_fun f a) (Id a)).     (* Equivalently, [un_opyoneda_0gpd a _ f]. *)
  set (gb := (cate_fun f^-1$ b) (Id b)). (* Equivalently, [un_opyoneda_0gpd b _ f^-1$]. *)
  srapply (cate_adjointify fa gb).
  (* [opyoneda_0gpd] is defined by postcomposition, so [opyoneda_isretr_0gpd] simplifies both LHSs.*)
  - exact (opyoneda_isretr_0gpd _ _ f^-1$ a fa $@ cat_eissect (f a) (Id a)).
  - exact (opyoneda_isretr_0gpd _ _ f     b gb $@ cat_eisretr (f b) (Id b)).
Defined.

(** Since [opyon_0gpd] is a 1-functor, postcomposition with a [cat_equiv] is an equivalence between the hom 0-groupoids. Note that we do not require [HasMorExt], as [equiv_postcompose_cat_equiv] does. *)
Definition equiv_postcompose_cat_equiv_0gpd {A : Type} `{HasEquivs A}
  {x y z : A} (f : y $<~> z)
  : opyon_0gpd x y $<~> opyon_0gpd x z
  := emap (opyon_0gpd x) f.

(** The dual result, which is used in the next result. *)
Definition equiv_precompose_cat_equiv_0gpd {A : Type} `{HasEquivs A}
  {x y z : A} (f : x $<~> y)
  : opyon_0gpd y z $<~> opyon_0gpd x z
  := @equiv_postcompose_cat_equiv_0gpd A^op _ _ _ _ _ z y x f.

(** A converse to [opyon_equiv_0gpd].  Together, we get a logical equivalence between [b $<~> a] and [opyon_0gpd a $<~> opyon_0gpd b], without [HasMorExt]. *)
Definition natequiv_opyon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (e : b $<~> a)
  : opyon1_0gpd a $<~> opyon1_0gpd b.
Proof.
  snapply Build_NatEquiv.
  - intro c; exact (equiv_precompose_cat_equiv_0gpd e).
  - tapply is1natural_opyoneda_0gpd.
Defined.

(** ** The contravariant Yoneda lemma *)

(** We can deduce this from the covariant version with some boilerplate. *)

Definition yon {A : Type} `{IsGraph A} (a : A) : A^op -> Type
  := opyon (A:=A^op) a.

Instance is0functor_yon {A : Type} `{H : Is01Cat A} (a : A)
  : Is0Functor (yon a)
  := is0functor_opyon (A:=A^op) a.

Instance is1functor_yon {A : Type} `{H : Is1Cat A} `{!HasMorExt A} (a : A)
  : Is1Functor (yon a)
  := is1functor_opyon (A:=A^op) a.

Definition yoneda {A : Type} `{Is01Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
  : F a -> (yon a $=> F)
  := @opyoneda (A^op) _ _ a F _.

Definition un_yoneda {A : Type} `{Is01Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
  : (yon a $=> F) -> F a
  := un_opyoneda (A:=A^op) a F.

Instance is1natural_yoneda {A : Type} `{Is1Cat A} (a : A)
       (F : A^op -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (yon a) F (yoneda a F x)
  := is1natural_opyoneda (A:=A^op) a F x.

Definition yoneda_isinj {A : Type} `{Is1Cat A} (a : A)
  (F : A^op -> Type) `{!Is0Functor F, !Is1Functor F}
  (x x' : F a) (p : forall b, yoneda a F x b == yoneda a F x' b)
  : x = x'
  := opyoneda_isinj (A:=A^op) a F x x' p.

Definition yon_faithful {A : Type} `{Is1Cat_Strong A}
  (a b : A) (f g : b $-> a)
  (p : forall (c : A) (h : c $-> b), f $o h = g $o h)
  : f = g
  := opyon_faithful (A:=A^op) b a f g p.

Definition yoneda_issect {A : Type} `{Is1Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : un_yoneda a F (yoneda a F x) = x
  := opyoneda_issect (A:=A^op) a F x.

Definition yoneda_isretr {A : Type} `{Is1Cat_Strong A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
           (* Without the hint here, Coq guesses to first project from [Is1Cat_Strong A] and then pass to opposites, whereas what we need is to first pass to opposites and then project. *)
           `{@Is1Functor _ _ _ _ _ (is1cat_is1cat_strong A^op) _ _ _ _ F _}
           (alpha : yon a $=> F) {alnat : Is1Natural (yon a) F alpha}
           (b : A)
  : yoneda a F (un_yoneda a F alpha) b $== alpha b
  := opyoneda_isretr (A:=A^op) a F alpha b.

Definition yon_cancel {A : Type} `{Is01Cat A} (a b : A)
  : (yon a $=> yon b) -> (a $-> b)
  := un_yoneda a (yon b).

Definition yon1 {A : Type} `{Is01Cat A} (a : A) : Fun01 A^op Type
  := opyon1 (A:=A^op) a.

Definition yon11 {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A) : Fun11 A^op Type
  := opyon11 (A:=A^op) a.

Definition yon_equiv {A : Type} `{HasEquivs A} `{!Is1Cat_Strong A}
           (a b : A)
  : (yon1 a $<~> yon1 b) -> (a $<~> b)
  := opyon_equiv (A:=A^op).

Definition natequiv_yon_equiv {A : Type} `{HasEquivs A}
  `{!HasMorExt A} (a b : A)
  : (a $<~> b) -> (yon1 a $<~> yon1 b)
  := natequiv_opyon_equiv (A:=A^op).

(** ** The contravariant Yoneda lemma using 0-groupoids *)

Definition yon_0gpd {A : Type} `{Is1Cat A} (a : A) : A^op -> ZeroGpd
  := opyon_0gpd (A:=A^op) a.

Instance is0functor_yon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is0Functor (yon_0gpd a)
  := is0functor_opyon_0gpd (A:=A^op) a.

Instance is1functor_yon_0gpd {A : Type} `{Is1Cat A} (a : A)
  : Is1Functor (yon_0gpd a)
  := is1functor_opyon_0gpd (A:=A^op) a.

Definition yoneda_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A^op -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  : F a -> (yon_0gpd a $=> F)
  := opyoneda_0gpd (A:=A^op) a F.

Definition un_yoneda_0gpd {A : Type} `{Is1Cat A}
  (a : A) (F : A^op -> ZeroGpd) {ff : Is0Functor F}
  : (yon_0gpd a $=> F) -> F a
  := un_opyoneda_0gpd (A:=A^op) a F.

Instance is1natural_yoneda_0gpd {A : Type} `{Is1Cat A}
  (a : A) (F : A^op -> ZeroGpd) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (yon_0gpd a) F (yoneda_0gpd a F x)
  := is1natural_opyoneda_0gpd (A:=A^op) a F x.

Definition yoneda_isinj_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A^op -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (x x' : F a) (p : forall b : A, yoneda_0gpd a F x b $== yoneda_0gpd a F x' b)
  : x $== x'
  := opyoneda_isinj_0gpd (A:=A^op) a F x x' p.

Definition yon_faithful_0gpd {A : Type} `{Is1Cat A} (a b : A)
  (f g : b $-> a) (p : forall (c : A) (h : c $-> b), f $o h $== g $o h)
  : f $== g
  := opyon_faithful_0gpd (A:=A^op) b a f g p.

Definition yoneda_issect_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A^op -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (x : F a)
  : un_yoneda_0gpd a F (yoneda_0gpd a F x) $== x
  := opyoneda_issect_0gpd (A:=A^op) a F x.

Definition yoneda_isretr_0gpd {A : Type} `{Is1Cat A} (a : A)
  (F : A^op -> ZeroGpd) `{!Is0Functor F, !Is1Functor F}
  (alpha : yon_0gpd a $=> F) {alnat : Is1Natural (yon_0gpd a) F alpha}
  (b : A)
  : yoneda_0gpd a F (un_yoneda_0gpd a F alpha) b $== alpha b
  := opyoneda_isretr_0gpd (A:=A^op) a F alpha b.

Definition yon_cancel_0gpd {A : Type} `{Is1Cat A} (a b : A)
  : (yon_0gpd a $=> yon_0gpd b) -> (a $-> b)
  := opyon_cancel_0gpd (A:=A^op) a b.

Definition yon1_0gpd {A : Type} `{Is1Cat A} (a : A) : Fun11 A^op ZeroGpd
  := opyon1_0gpd (A:=A^op) a.

Definition yon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (f : yon1_0gpd a $<~> yon1_0gpd b)
  : a $<~> b
  := opyon_equiv_0gpd (A:=A^op) f.

Definition natequiv_yon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (e : a $<~> b)
  : yon1_0gpd (A:=A) a $<~> yon1_0gpd b
  := natequiv_opyon_equiv_0gpd (A:=A^op) (e : CatEquiv (A:=A^op) b a).
