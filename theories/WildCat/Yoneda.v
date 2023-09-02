(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Universe.
Require Import WildCat.Opposite.
Require Import WildCat.FunctorCat.
Require Import WildCat.NatTrans.
Require Import WildCat.Prod.
Require Import WildCat.ZeroGroupoid.

(** ** Two-variable hom-functors *)

Global Instance is0functor_hom {A} `{Is01Cat A}
  : @Is0Functor (A^op * A) Type _ _ (uncurry (@Hom A _)).
Proof.
  apply Build_Is0Functor.
  intros [a1 a2] [b1 b2] [f1 f2] g; cbn in *.
  exact (f2 $o g $o f1).
Defined.

(** This requires morphism extensionality! *)
Global Instance is1functor_hom {A} `{HasMorExt A}
  : @Is1Functor (A^op * A) Type _ _ _ _ _ _ _ _ (uncurry (@Hom A _)) _.
Proof.
  apply Build_Is1Functor.
  - intros [a1 a2] [b1 b2] [f1 f2] [g1 g2] [p1 p2] q;
      unfold fst, snd in *.
    apply path_hom.
    refine (((p2 $@R q) $@R _) $@ ((g2 $o q) $@L p1)).
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
    refine (cat_assoc_opp _ _ _).
Defined.

Definition fun01_hom {A} `{Is01Cat A}
  : Fun01 (A^op * A) Type
  := @Build_Fun01 _ _ _ _ _ is0functor_hom.

(** ** The covariant Yoneda lemma *)

(** This is easier than the contravariant version because it doesn't involve any "op"s. *)

Definition opyon {A : Type} `{IsGraph A} (a : A) : A -> Type
  := fun b => (a $-> b).

Global Instance is0functor_opyon {A : Type} `{Is01Cat A} (a : A)
  : Is0Functor (opyon a).
Proof.
  apply Build_Is0Functor.
  unfold opyon; intros b c f g; cbn in *.
  exact (f $o g).
Defined.

Global Instance is1functor_opyon {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A)
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

Global Instance is1natural_opyoneda {A : Type} `{Is1Cat A}
  (a : A) (F : A -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (opyon a) F (opyoneda a F x).
Proof.
  unfold opyon, opyoneda; intros b c f g; cbn in *.
  exact (fmap_comp F g f x).
Defined.

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

(** Specialization to "full-faithfulness" of the Yoneda embedding.  (In quotes because, again, incoherence means we can't recover the witness of naturality.)  *)
Definition opyon_cancel {A : Type} `{Is01Cat A} (a b : A)
  : (opyon a $=> opyon b) -> (b $-> a)
  := un_opyoneda a (opyon b).

Definition opyon1 {A : Type} `{Is01Cat A} (a : A) : Fun01 A Type.
Proof.
  rapply (Build_Fun01 _ _ (opyon a)).
Defined.

Definition opyon11 {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A) : Fun11 A Type.
Proof.
  rapply (Build_Fun11 _ _ (opyon a)).
Defined.

(** We can also deduce "full-faithfulness" on equivalences. *)
Definition opyon_equiv {A : Type} `{HasEquivs A} `{!Is1Cat_Strong A}
           (a b : A)
  : (opyon1 a $<~> opyon1 b) -> (b $<~> a).
Proof.
  intros f.
  refine (cate_adjointify (f a (Id a)) (f^-1$ b (Id b)) _ _) ;
    apply GpdHom_path;
      pose proof (is1natural_natequiv _ _ f);
      pose proof (is1natural_natequiv _ _ f^-1$);
      cbn in *.
  - refine ((isnat (fun a => (f a)^-1$) (f a (Id a)) (Id b))^ @ _); cbn.
    refine (_ @ cate_issect (f a) (Id a)); cbn.
    apply ap.
    srapply cat_idr_strong.
  - refine ((isnat (cat_equiv_natequiv _ _ f) (f^-1$ b (Id b)) (Id a))^ @ _); cbn.
    refine (_ @ cate_isretr (f b) (Id b)); cbn.
    apply ap.
    srapply cat_idr_strong.
Defined.

Definition natequiv_opyon_equiv {A : Type} `{HasEquivs A}
  `{!HasMorExt A} (a b : A)
  : (b $<~> a) -> (opyon1 a $<~> opyon1 b).
Proof.
  intro e.
  snrapply Build_NatEquiv.
  - intros c.
    exact (equiv_precompose_cat_equiv e).
  - rapply is1natural_opyoneda.
Defined.

(** We define a version of [opyon] that lands in 0-groupoids, which we regard as setoids. *)
Definition opyon_0gpd {A : Type} `{Is1Cat A} (a : A) : Fun01 A ZeroGpd.
Proof.
  snrapply Build_Fun01.
  - intro b.
    rapply (Build_ZeroGpd (opyon a b)).
  - snrapply Build_Is0Functor.
    intros b c f; cbn beta.
    snrapply Build_ZeroGpdMorphism; cbn.
    + exact (fmap (opyon a) f).
    + apply is0functor_postcomp.
Defined.

(** A version of the covariant Yoneda lemma which regards [opyon] as a functor taking values in 0-groupoids, using the 1-category structure on [ZeroGpd] in [ZeroGroupoid.v].  Instead of assuming that each [f c : (a $-> c) -> (b $-> c)] is an equivalence of types, it only needs to be an equivalence of 0-groupoids.  For example, this means that we have a map [g c : (b $-> c) -> (a $-> c)] such that for each [k : a $-> c], [g c (f c k) $== k], rather than [g c (f c k) = k] as the version with types requires.  Similarly, the naturality is up to 2-cells, instead of up to paths.  This allows us to avoid [Funext] and [HasMorExt] when using this result.  As a side benefit, we also don't require that [A] is strong. *)
Definition opyon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (f : opyon_0gpd a $<~> opyon_0gpd b)
  : b $<~> a.
Proof.
  set (g := f^-1$).
  srapply (cate_adjointify (f a (Id a)) (g b (Id b))).
  - pose proof (gn := is1natural_natequiv _ _ g).
    refine ((isnat (alnat:=gn) g (f a (Id a)) (Id b))^$ $@ _).
    refine (fmap (g a) (cat_idr (f a (Id a))) $@ _).
    1: rapply is0functor_zerogpd_fun.
    1: exact _.
    rapply zerogpd_eissect.
  - pose proof (fn := is1natural_natequiv _ _ f).
    refine ((isnat (alnat:=fn) f (g b (Id b)) (Id a))^$ $@ _).
    refine (fmap (f b) (cat_idr (g b (Id b))) $@ _).
    1: rapply is0functor_zerogpd_fun.
    1: exact _.
    rapply zerogpd_eisretr.
  (* Not sure why typeclass inference doesn't find [is1natural_natequiv] and [is0functor_zerogpd_fun] above. *)
Defined.

(** Precomposition with a [cat_equiv] is an equivalence between the hom 0-groupoids. Note that we do not require [HasMorExt], as [equiv_precompose_cat_equiv] does. *)
Definition equiv_precompose_cat_equiv_0gpd {A : Type} `{HasEquivs A}
  {x y z : A} (f : x $<~> y)
  : opyon_0gpd y z $<~> opyon_0gpd x z.
Proof.
  snrapply cate_adjointify.
  - snrapply Build_ZeroGpdMorphism.
    1: exact (cat_precomp z f).
    exact _.
  - snrapply Build_ZeroGpdMorphism.
    1: exact (cat_precomp z f^-1$).
    exact _.
  - cbn.
    intro g.
    unfold cat_precomp.
    apply compose_hV_h.
  - cbn.
    intro g.
    unfold cat_precomp.
    apply compose_hh_V.
Defined.

(** A converse to [opyon_equiv_0gpd].  Together, we get a logical equivalence between [b $<~> a] and [opyon_0gpd a $<~> opyon_0gpd b].  Note again that the converse requires [HasMorExt] when using [opyon1]. *)
Definition natequiv_opyon_equiv_0gpd {A : Type} `{HasEquivs A}
  {a b : A} (e : b $<~> a)
  : opyon_0gpd a $<~> opyon_0gpd b.
Proof.
  snrapply Build_NatEquiv.
  - intro c; exact (equiv_precompose_cat_equiv_0gpd e).
  - intros c d f g; cbn.
    unfold cat_precomp.
    apply cat_assoc.
Defined.

(** ** The contravariant Yoneda lemma *)

(** We can deduce this from the covariant version with some boilerplate. *)

Definition yon {A : Type} `{IsGraph A} (a : A) : A^op -> Type
  := @opyon (A^op) _ a.

Global Instance is0functor_yon {A : Type} `{H : Is01Cat A} (a : A)
  : Is0Functor (yon a).
Proof.
  apply is0functor_opyon.
Defined.

Global Instance is1functor_yon {A : Type} `{H : Is1Cat A} `{!HasMorExt A} (a : A)
  : Is1Functor (yon a).
Proof.
  rapply is1functor_opyon.
Defined.

Definition yoneda {A : Type} `{Is01Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
  : F a -> (yon a $=> F)
  := @opyoneda (A^op) _ _ a F _.

Definition un_yoneda {A : Type} `{Is01Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
  : (yon a $=> F) -> F a
  := @un_opyoneda (A^op) _ _ a F _.

Global Instance is1natural_yoneda {A : Type} `{Is1Cat A} (a : A)
       (F : A^op -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : Is1Natural (yon a) F (yoneda a F x)
  := @is1natural_opyoneda (A^op) _ _ _ _ a F _ _ x.

Definition yoneda_issect {A : Type} `{Is1Cat A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F, !Is1Functor F} (x : F a)
  : un_yoneda a F (yoneda a F x) = x
  := @opyoneda_issect (A^op) _ _ _ _ a F _ _ x.

Definition yoneda_isretr {A : Type} `{Is1Cat_Strong A} (a : A)
           (F : A^op -> Type) `{!Is0Functor F}
           (* Without the hint here, Coq guesses to first project from [Is1Cat_Strong A] and then pass to opposites, whereas what we need is to first pass to opposites and then project. *)
           `{@Is1Functor _ _ _ _ _ (is1cat_is1cat_strong A^op) _ _ _ _ F _}
           (alpha : yon a $=> F) {alnat : Is1Natural (yon a) F alpha}
           (b : A)
  : yoneda a F (un_yoneda a F alpha) b $== alpha b
  := @opyoneda_isretr A^op _ _ _ (is1cat_strong_op A) a F _ _ alpha alnat b.

Definition yon_cancel {A : Type} `{Is01Cat A} (a b : A)
  : (yon a $=> yon b) -> (a $-> b)
  := un_yoneda a (yon b).

Definition yon1 {A : Type} `{Is01Cat A} (a : A) : Fun01 A^op Type
  := @opyon1 A^op _ _ a.

Definition yon11 {A : Type} `{Is1Cat A} `{!HasMorExt A} (a : A) : Fun11 A^op Type
  := @opyon11 A^op _ _ _ _ _ a.

Definition yon_equiv {A : Type} `{HasEquivs A} `{!Is1Cat_Strong A}
           (a b : A)
  : (yon1 a $<~> yon1 b) -> (a $<~> b)
  := (@opyon_equiv A^op _ _ _ _ _ _ a b).

Definition natequiv_yon_equiv {A : Type} `{HasEquivs A}
  `{!HasMorExt A} (a b : A)
  : (a $<~> b) -> (yon1 a $<~> yon1 b)
  := (@natequiv_opyon_equiv A^op _ _ _ _ _ _ a b).
