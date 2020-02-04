(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.NatTrans.
Require Import WildCat.Sigma.

(** * Equivalences of 0-groupoids, and split essentially surjective functors *)

(** We could define these similarly for more general categories too, but we'd need to use [HasEquivs] and [$<~>] instead of [$==]. *)

Class SplEssSurj {A B : Type} `{Is0Gpd A, Is0Gpd B}
      (F : A -> B) `{!Is0Functor F} 
  := esssurj : forall b:B, { a:A & F a $== b }.

Arguments esssurj {A B _ _ _ _} F {_ _} b.

(** A 0-functor between 0-groupoids is an equivalence if it is essentially surjective and reflects the existence of morphisms.  This is "surjective and injective" in setoid-language.  (To define essential surjectivity for non-groupoids, we would need [HasEquivs] from [WildCat.Equiv]. *)
Class IsEquiv0Gpd {A B : Type} `{Is0Gpd A, Is0Gpd B}
      (F : A -> B) `{!Is0Functor F} :=
{
  esssurj_isequiv0gpd : SplEssSurj F ;
  essinj0 : forall (x y:A), (F x $== F y) -> (x $== y) ;
}.

Global Existing Instance esssurj_isequiv0gpd.
Arguments essinj0 {A B _ _ _ _} F {_ _ x y} f.

Definition equiv0gpd_inv {A B : Type} (F : A -> B) `{IsEquiv0Gpd A B F} : B -> A
  := fun b => (esssurj F b).1.

(** Equivalences have inverses *)

Global Instance is0functor_equiv0gpd_inv
       {A B : Type} (F : A -> B) `{IsEquiv0Gpd A B F}
  : Is0Functor (equiv0gpd_inv F).
Proof.
  constructor; intros x y f.
  pose (p := (esssurj F x).2).
  pose (q := (esssurj F y).2).
  cbn in *.
  pose (f' := p $@ f $@ q^$).
  exact (essinj0 F f').
Defined.

(** The inverse is an inverse, up to unnatural transformations *)

Definition eisretr0gpd_inv {A B : Type} (F : A -> B) `{IsEquiv0Gpd A B F}
  : F o equiv0gpd_inv F $=> idmap.
Proof.
  intros b.
  exact ((esssurj F b).2).
Defined.

Definition eissect0gpd_inv {A B : Type} (F : A -> B) `{IsEquiv0Gpd A B F}
  : equiv0gpd_inv F o F $=> idmap.
Proof.
  intros a.
  apply (essinj0 F).
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

Definition isequiv0gpd_transf {A B : Type} {F : A -> B} {G : A -> B}
           `{IsEquiv0Gpd A B F} `{!Is0Functor G} (alpha : G $=> F)
  : IsEquiv0Gpd G.
Proof.
  constructor.
  - apply (isesssurj_transf alpha).
  - intros x y f.
    apply (essinj0 F).
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

  Global Instance isequiv0gpd_compose
         `{!IsEquiv0Gpd G, !IsEquiv0Gpd F}
    : IsEquiv0Gpd (G o F).
  Proof.
    constructor.
    - exact _.
    - intros x y f.
      apply (essinj0 F).
      exact (essinj0 G f).
  Defined.

  Definition cancelL_isesssurj
             `{!IsEquiv0Gpd G, !SplEssSurj (G o F)}
    : SplEssSurj F.
  Proof.
    intros b.
    exists ((esssurj (G o F) (G b)).1).
    apply (essinj0 G).
    exact ((esssurj (G o F) (G b)).2).
  Defined.

  Definition iffL_isesssurj `{!IsEquiv0Gpd G}
    : SplEssSurj (G o F) <-> SplEssSurj F.
  Proof.
    split; [ apply @cancelL_isesssurj | apply @isesssurj_compose ]; exact _.
  Defined.

  Definition cancelL_isequiv0gpd
             `{!IsEquiv0Gpd G, !IsEquiv0Gpd (G o F)}
    : IsEquiv0Gpd F.
  Proof.
    constructor.
    - apply cancelL_isesssurj.
    - intros x y f.
      exact (essinj0 (G o F) (fmap G f)).
  Defined.

  Definition iffL_isequiv0gpd `{!IsEquiv0Gpd G}
    : IsEquiv0Gpd (G o F) <-> IsEquiv0Gpd F.
  Proof.
    split; [ apply @cancelL_isequiv0gpd | apply @isequiv0gpd_compose ]; exact _.
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

  Definition cancelR_isequiv0gpd
             `{!IsEquiv0Gpd F, !IsEquiv0Gpd (G o F)}
    : IsEquiv0Gpd G.
  Proof.
    constructor.
    - apply cancelR_isesssurj.
    - intros x y f.
      pose (p := (esssurj F x).2).
      pose (q := (esssurj F y).2).
      cbn in *.
      refine (p^$ $@ _ $@ q).
      apply (fmap F).
      apply (essinj0 (G o F)).
      refine (_ $@ f $@ _).
      + exact (fmap G p).
      + exact (fmap G q^$).
  Defined.

  Definition iffR_isequiv0gpd `{!IsEquiv0Gpd F}
    : IsEquiv0Gpd (G o F) <-> IsEquiv0Gpd G.
  Proof.
    split; [ apply @cancelR_isequiv0gpd | intros; apply @isequiv0gpd_compose ]; exact _.
  Defined.

End ComposeAndCancel.

(** In particular, essential surjectivity and being an equivalence transfer across commutative squares of functors. *)
Definition isesssurj_iff_commsq {A B C D : Type}
           {F : A -> B} {G : C -> D} {H : A -> C} {K : B -> D}
           `{IsEquiv0Gpd A C H} `{IsEquiv0Gpd B D K}
           `{!Is0Functor F} `{!Is0Functor G}
           (p : K o F $=> G o H)
  : SplEssSurj F <-> SplEssSurj G.
Proof.
  split; intros ?.
  - serapply (cancelR_isesssurj G H); try exact _.
    apply (isesssurj_transf (fun a => (p a)^$)).
  - serapply (cancelL_isesssurj K F); try exact _.
    apply (isesssurj_transf p).
Defined.

Definition isequiv0gpd_iff_commsq {A B C D : Type}
           {F : A -> B} {G : C -> D} {H : A -> C} {K : B -> D}
           `{IsEquiv0Gpd A C H} `{IsEquiv0Gpd B D K}
           `{!Is0Functor F} `{!Is0Functor G}
           (p : K o F $=> G o H)
  : IsEquiv0Gpd F <-> IsEquiv0Gpd G.
Proof.
  split; intros ?.
  - serapply (cancelR_isequiv0gpd G H); try exact _.
    apply (isequiv0gpd_transf (fun a => (p a)^$)).
  - serapply (cancelL_isequiv0gpd K F); try exact _.
    apply (isequiv0gpd_transf p).
Defined.

(** Equivalences and essential surjectivity are preserved by sigmas (for now, just over constant bases), and essential surjectivity at least is also reflected. *)

Definition isesssurj_iff_sigma {A : Type} (B C : A -> Type)
       {bc : forall a, Is01Cat (B a)} {bg : forall a, Is0Gpd (B a)}
       {cc : forall a, Is01Cat (C a)} {cg : forall a, Is0Gpd (C a)}
       (F : forall a, B a -> C a)
       {ff : forall a, Is0Functor (F a)}
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

Definition isequiv0gpd_sigma {A : Type} (B C : A -> Type)
       {bc : forall a, Is01Cat (B a)} {bg : forall a, Is0Gpd (B a)}
       {cc : forall a, Is01Cat (C a)} {cg : forall a, Is0Gpd (C a)}
       (F : forall a, B a -> C a)
       {ff : forall a, Is0Functor (F a)} {fs : forall a, IsEquiv0Gpd (F a)}
  : IsEquiv0Gpd (fun (x:sig B) => (x.1 ; F x.1 x.2)).
Proof.
  constructor.
  - apply isesssurj_iff_sigma; exact _.
  - intros [a1 b1] [a2 b2] [p f]; cbn in *.
    destruct p; cbn in *.
    exists idpath; cbn.
    exact (essinj0 (F a1) f).
Defined.
