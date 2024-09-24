(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.Overture Basics.Tactics Basics.Iff.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Sigma.

(** * Equivalences of 0-groupoids, and split essentially surjective functors *)

(** For a logically equivalent definition of equivalences of 0-groupoids, see ZeroGroupoid.v. *)

(** We could define these similarly for more general categories too, but we'd need to use [HasEquivs] and [$<~>] instead of [$==]. *)

Class SplEssSurj {A B : Type} `{Is0Gpd A, Is0Gpd B}
      (F : A -> B) `{!Is0Functor F} 
  := esssurj : forall b:B, { a:A & F a $== b }.

Arguments esssurj {A B _ _ _ _ _ _} F {_ _} b.

(** A 0-functor between 0-groupoids is an "equivalence" if it is essentially surjective and reflects the existence of morphisms.  This is "surjective and injective" in setoid-language, so we use the name [IsSurjInj].  (To define essential surjectivity for non-groupoids, we would need [HasEquivs] from [WildCat.Equiv]. *)
Class IsSurjInj {A B : Type} `{Is0Gpd A, Is0Gpd B}
      (F : A -> B) `{!Is0Functor F} :=
{
  esssurj_issurjinj : SplEssSurj F ;
  essinj : forall (x y:A), (F x $== F y) -> (x $== y) ;
}.

Global Existing Instance esssurj_issurjinj.
Arguments essinj {A B _ _ _ _ _ _} F {_ _ x y} f.

Definition surjinj_inv {A B : Type} (F : A -> B) `{IsSurjInj A B F} : B -> A
  := fun b => (esssurj F b).1.

(** Some of the results below also follow from the logical equivalence with [IsEquiv_0Gpd] and the fact that [ZeroGpd] satisfies [HasEquivs].  But it is sometimes awkward to deduce the results this way, mostly because [ZeroGpd] requires bundled objects rather than typeclass instances. *)

(** Equivalences have inverses *)

Global Instance is0functor_surjinj_inv
       {A B : Type} (F : A -> B) `{IsSurjInj A B F}
  : Is0Functor (surjinj_inv F).
Proof.
  constructor; intros x y f.
  pose (p := (esssurj F x).2).
  pose (q := (esssurj F y).2).
  cbn in *.
  pose (f' := p $@ f $@ q^$).
  exact (essinj F f').
Defined.

(** The inverse is an inverse, up to unnatural transformations *)

Definition eisretr0gpd_inv {A B : Type} (F : A -> B) `{IsSurjInj A B F}
  : F o surjinj_inv F $=> idmap.
Proof.
  intros b.
  exact ((esssurj F b).2).
Defined.

Definition eissect0gpd_inv {A B : Type} (F : A -> B) `{IsSurjInj A B F}
  : surjinj_inv F o F $=> idmap.
Proof.
  intros a.
  apply (essinj F).
  apply eisretr0gpd_inv.
Defined.

(** Essentially surjective functors and equivalences are preserved by transformations. *)
Definition isesssurj_transf {A B : Type} {F : A -> B} {G : A -> B}
           `{SplEssSurj A B F} `{!Is0Functor G} (alpha : G $=> F)
  : SplEssSurj G.
Proof.
  intros b.
  exists ((esssurj F b).1).
  refine (_ $@ (esssurj F b).2).
  apply alpha.
Defined.

Definition issurjinj_transf {A B : Type} {F : A -> B} {G : A -> B}
           `{IsSurjInj A B F} `{!Is0Functor G} (alpha : G $=> F)
  : IsSurjInj G.
Proof.
  constructor.
  - apply (isesssurj_transf alpha).
  - intros x y f.
    apply (essinj F).
    refine (_ $@ f $@ _).
    + symmetry; apply alpha.
    + apply alpha.
Defined.

(** Equivalences compose and cancel with each other and with essentially surjective functors. *)

Section ComposeAndCancel.
  Context {A B C} `{Is0Gpd A, Is0Gpd B, Is0Gpd C}
       (G : B -> C) (F : A -> B) `{!Is0Functor G, !Is0Functor F}.

  Global Instance isesssurj_compose
         `{!SplEssSurj G, !SplEssSurj F}
    : SplEssSurj (G o F).
  Proof.
    intros c.
    exists ((esssurj F (esssurj G c).1).1).
    refine (_ $@ (esssurj G c).2).
    apply (fmap G).
    apply (esssurj F).
  Defined.

  Global Instance issurjinj_compose
         `{!IsSurjInj G, !IsSurjInj F}
    : IsSurjInj (G o F).
  Proof.
    constructor.
    - exact _.
    - intros x y f.
      apply (essinj F).
      exact (essinj G f).
  Defined.

  Definition cancelL_isesssurj
             `{!IsSurjInj G, !SplEssSurj (G o F)}
    : SplEssSurj F.
  Proof.
    intros b.
    exists ((esssurj (G o F) (G b)).1).
    apply (essinj G).
    exact ((esssurj (G o F) (G b)).2).
  Defined.

  Definition iffL_isesssurj `{!IsSurjInj G}
    : SplEssSurj (G o F) <-> SplEssSurj F.
  Proof.
    split; [ apply @cancelL_isesssurj | apply @isesssurj_compose ]; exact _.
  Defined.

  Definition cancelL_issurjinj
             `{!IsSurjInj G, !IsSurjInj (G o F)}
    : IsSurjInj F.
  Proof.
    constructor.
    - apply cancelL_isesssurj.
    - intros x y f.
      exact (essinj (G o F) (fmap G f)).
  Defined.

  Definition iffL_issurjinj `{!IsSurjInj G}
    : IsSurjInj (G o F) <-> IsSurjInj F.
  Proof.
    split; [ apply @cancelL_issurjinj | apply @issurjinj_compose ]; exact _.
  Defined.

  Definition cancelR_isesssurj `{!SplEssSurj (G o F)}
    : SplEssSurj G.
  Proof.
    intros c.
    exists (F (esssurj (G o F) c).1).
    exact ((esssurj (G o F) c).2).
  Defined.

  Definition iffR_isesssurj `{!SplEssSurj F}
    : SplEssSurj (G o F) <-> SplEssSurj G.
  Proof.
    split; [ apply @cancelR_isesssurj | intros; apply @isesssurj_compose ]; exact _.
  Defined.

  Definition cancelR_issurjinj
             `{!IsSurjInj F, !IsSurjInj (G o F)}
    : IsSurjInj G.
  Proof.
    constructor.
    - apply cancelR_isesssurj.
    - intros x y f.
      pose (p := (esssurj F x).2).
      pose (q := (esssurj F y).2).
      cbn in *.
      refine (p^$ $@ _ $@ q).
      apply (fmap F).
      apply (essinj (G o F)).
      refine (_ $@ f $@ _).
      + exact (fmap G p).
      + exact (fmap G q^$).
  Defined.

  Definition iffR_issurjinj `{!IsSurjInj F}
    : IsSurjInj (G o F) <-> IsSurjInj G.
  Proof.
    split; [ apply @cancelR_issurjinj | intros; apply @issurjinj_compose ]; exact _.
  Defined.

End ComposeAndCancel.

(** In particular, essential surjectivity and being an equivalence transfer across commutative squares of functors. *)
Definition isesssurj_iff_commsq {A B C D : Type}
           {F : A -> B} {G : C -> D} {H : A -> C} {K : B -> D}
           `{IsSurjInj A C H} `{IsSurjInj B D K}
           `{!Is0Functor F} `{!Is0Functor G}
           (p : K o F $=> G o H)
  : SplEssSurj F <-> SplEssSurj G.
Proof.
  split; intros ?.
  - srapply (cancelR_isesssurj G H); try exact _.
    apply (isesssurj_transf (fun a => (p a)^$)).
  - srapply (cancelL_isesssurj K F); try exact _.
    apply (isesssurj_transf p).
Defined.

Definition issurjinj_iff_commsq {A B C D : Type}
           {F : A -> B} {G : C -> D} {H : A -> C} {K : B -> D}
           `{IsSurjInj A C H} `{IsSurjInj B D K}
           `{!Is0Functor F} `{!Is0Functor G}
           (p : K o F $=> G o H)
  : IsSurjInj F <-> IsSurjInj G.
Proof.
  split; intros ?.
  - srapply (cancelR_issurjinj G H); try exact _.
    apply (issurjinj_transf (fun a => (p a)^$)).
  - srapply (cancelL_issurjinj K F); try exact _.
    apply (issurjinj_transf p).
Defined.

(** Equivalences and essential surjectivity are preserved by sigmas (for now, just over constant bases), and essential surjectivity at least is also reflected. *)

Definition isesssurj_iff_sigma {A : Type} (B C : A -> Type)
 `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)} `{forall a, Is0Gpd (B a)}
 `{forall a, IsGraph (C a)} `{forall a, Is01Cat (C a)} `{forall a, Is0Gpd (C a)}
  (F : forall a, B a -> C a) {ff : forall a, Is0Functor (F a)}
  : SplEssSurj (fun (x:sig B) => (x.1 ; F x.1 x.2))
    <-> (forall a, SplEssSurj (F a)).
Proof.
  split.
  - intros fs a c.
    pose (s := fs (a;c)).
    destruct s as [[a' b] [p q]]; cbn in *.
    destruct p; cbn in q.
    exists b.
    exact q.
  - intros fs [a c].
    exists (a ; (esssurj (F a) c).1); cbn.
    exists idpath; cbn.
    exact ((esssurj (F a) c).2).
Defined.

Definition issurjinj_sigma {A : Type} (B C : A -> Type)
 `{forall a, IsGraph (B a)} `{forall a, Is01Cat (B a)} `{forall a, Is0Gpd (B a)}
 `{forall a, IsGraph (C a)} `{forall a, Is01Cat (C a)} `{forall a, Is0Gpd (C a)}
  (F : forall a, B a -> C a)
  `{forall a, Is0Functor (F a)} `{forall a, IsSurjInj (F a)}
  : IsSurjInj (fun (x:sig B) => (x.1 ; F x.1 x.2)).
Proof.
  constructor.
  - apply isesssurj_iff_sigma; exact _.
  - intros [a1 b1] [a2 b2] [p f]; cbn in *.
    destruct p; cbn in *.
    exists idpath; cbn.
    exact (essinj (F a1) f).
Defined.
