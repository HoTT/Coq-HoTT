Require Import Basics.Overture Basics.Tactics
               Basics.PathGroupoids.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd
               WildCat.Forall WildCat.Graph WildCat.Induced WildCat.FunctorCat.

(** * The wild 1-category of 0-groupoids. *)

(** Here we define a wild 1-category structure on the type of 0-groupoids.  We think of the 1-cells [g $== h] in a 0-groupoid [G] as a substitute for the paths [g = h], and so we closely follow the definitions used for the 1-category of types with [=] replaced by [$==].  In fact, the 1-category structure on types should be the pullback of the 1-category structure on 0-groupoids along a natural map [Type -> ZeroGpd] which sends [A] to [A] equipped with its path types.  A second motivating example is the 0-groupoid with underlying type [A -> B] and homotopies as the 1-cells.  The definitions chosen here exactly make the Yoneda lemma [opyon_equiv_0gpd] go through. *)

Record ZeroGpd := {
  carrier :> Type;
  isgraph_carrier :: IsGraph carrier;
  is01cat_carrier :: Is01Cat carrier;
  is0gpd_carrier :: Is0Gpd carrier;
}.

Definition zerogpd_graph (C : ZeroGpd) : Graph := {|
    graph_carrier := carrier C;
    isgraph_graph_carrier := isgraph_carrier C
  |}.

Instance isgraph_0gpd : IsGraph ZeroGpd := isgraph_induced zerogpd_graph.

Instance is01cat_0gpd : Is01Cat ZeroGpd := is01cat_induced zerogpd_graph.

Instance is2graph_0gpd : Is2Graph ZeroGpd := is2graph_induced zerogpd_graph.

Instance is1cat_0gpd : Is1Cat ZeroGpd.
Proof.
  snapply Build_Is1Cat.
  - intros G H.
    srapply Build_Is01Cat.
    + intro f. exact (fun x => Id (f x)).
    + intros f g h p q. exact (fun x => q x $@ p x).
  - intros G H.
    srapply Build_Is0Gpd.
    intros f g p. exact (fun x => (p x)^$).
  - intros G H K f.
    srapply Build_Is0Functor.
    intros g h p x.
    cbn.
    exact (fmap f (p x)).
  - intros G H K f.
    srapply Build_Is0Functor.
    intros g h p x.
    cbn.
    exact (p (f x)).
  - reflexivity. (* Associativity. *)
  - reflexivity. (* Associativity in opposite direction. *)
  - reflexivity. (* Left identity. *)
  - reflexivity. (* Right identity. *)
Defined.

(** We define equivalences of 0-groupoids as the bi-invertible maps, using [Cat_BiInv] and [Cat_IsBiInv].  This definition is chosen to provide what is needed for the Yoneda lemma, and because it specializes to one of the correct definitions for types. *)

Instance hasequivs_0gpd : HasEquivs ZeroGpd
  := cat_hasequivs ZeroGpd.

(** Coq can't find the composite of the coercions [cate_fun : G $<~> H >-> G $-> H] and [fun_0gpd : Morphism_0Gpd G H >-> G -> H], probably because it passes through the definitional equality of [G $-> H] and [Morphism_0Gpd G H].  I couldn't find a solution, so instead here is a helper function to manually do the coercion when needed. *)
Definition equiv_fun_0gpd {G H : ZeroGpd} (f : G $<~> H) : G -> H
  := fun01_F (cat_equiv_fun _ _ _ f).

(** ** Tools for manipulating equivalences of 0-groupoids

  Even though the proofs are easy, in certain contexts Coq gets confused about [$==] vs [$->], which makes it hard to prove this inline.  So we record them here. *)

(** Every equivalence is injective. *)
Definition isinj_equiv_0gpd {G H : ZeroGpd} (f : G $<~> H)
  {x y : G} (h : equiv_fun_0gpd f x $== equiv_fun_0gpd f y)
  : x $== y.
Proof.
  exact ((cat_eissect f x)^$ $@ fmap (equiv_fun_0gpd f^-1$) h $@ cat_eissect f y).
Defined.

(** This is one example of many things that could be ported from Basics/Equivalences.v. *)
Definition moveR_equiv_V_0gpd {G H : ZeroGpd} (f : G $<~> H) (x : H) (y : G) (p : x $== equiv_fun_0gpd f y)
  : equiv_fun_0gpd f^-1$ x $== y
  := fmap (equiv_fun_0gpd f^-1$) p $@ cat_eissect f y.

Definition moveL_equiv_V_0gpd {G H : ZeroGpd} (f : G $<~> H) (x : H) (y : G) (p : equiv_fun_0gpd f y $== x)
  : y $== equiv_fun_0gpd f^-1$ x
  := (cat_eissect f y)^$ $@ fmap (equiv_fun_0gpd f^-1$) p.

(** ** [f] is an equivalence of 0-groupoids iff [IsSurjInj f]

  We now give a different characterization of the equivalences of 0-groupoids, as the injective split essentially surjective 0-functors, which are defined in EquivGpd.  Advantages of this logically equivalent formulation are that it tends to be easier to prove in examples and that in some cases it is definitionally equal to [ExtensionAlong], which is convenient.  See Homotopy/Suspension.v and Algebra/AbGroups/Abelianization for examples. Advantages of the bi-invertible definition are that it reproduces a definition that is equivalent to [IsEquiv] when applied to types, assuming [Funext].  It also works in any 1-category. *)

(** Every equivalence is injective and split essentially surjective. *)
Instance issurjinj_equiv_0gpd {G H : ZeroGpd} (f : G $<~> H)
  : IsSurjInj (equiv_fun_0gpd f).
Proof.
  econstructor.
  - intro y.
    exists (equiv_fun_0gpd f^-1$ y).
    tapply cat_eisretr.
  - apply isinj_equiv_0gpd.
Defined.

(** Conversely, every injective split essentially surjective 0-functor is an equivalence.  In practice, this is often the easiest way to prove that a functor is an equivalence. *)
Definition isequiv_0gpd_issurjinj {G H : ZeroGpd} (F : G $-> H)
  {e : IsSurjInj F}
  : Cat_IsBiInv F.
Proof.
  destruct e as [e0 e1]; unfold SplEssSurj in e0.
  stapply catie_adjointify.
  - snapply Build_Fun01.
    1: exact (fun y => (e0 y).1).
    snapply Build_Is0Functor; cbn beta.
    intros y1 y2 m.
    apply e1.
    exact ((e0 y1).2 $@ m $@ ((e0 y2).2)^$).
  - cbn. exact (fun a => (e0 a).2).
  - cbn.  intro x.
    apply e1.
    apply e0.
Defined.

(** [I]-indexed products for an [I]-indexed family of 0-groupoids. *)
Definition prod_0gpd (I : Type) (G : I -> ZeroGpd) : ZeroGpd.
Proof.
  rapply (Build_ZeroGpd (forall i, G i)).
Defined.

(** The [i]-th projection from the [I]-indexed product of 0-groupoids. *)
Definition prod_0gpd_pr {I : Type} {G : I -> ZeroGpd}
  : forall i, prod_0gpd I G $-> G i.
Proof.
  intros i.
  snapply Build_Fun01.
  1: exact (fun f => f i).
  snapply Build_Is0Functor; cbn beta.
  intros f g p.
  exact (p i).
Defined.

(** The universal property of the product of 0-groupoids holds almost definitionally. *)
Definition equiv_prod_0gpd_corec {I : Type} {G : ZeroGpd} {H : I -> ZeroGpd}
  : (forall i, G $-> H i) <~> (G $-> prod_0gpd I H).
Proof.
  snapply Build_Equiv.
  { intro f.
    snapply Build_Fun01.
    1: exact (fun x i => f i x).
    snapply Build_Is0Functor; cbn beta.
    intros x y p i; simpl.
    exact (fmap (f i) p). }
  snapply Build_IsEquiv.
  - intro f.
    intros i.
    exact (prod_0gpd_pr i $o f).
  - intro f.
    reflexivity.
  - intro f.
    reflexivity.
  - reflexivity.
Defined.

(** Indexed products of groupoids with equivalent indices and fiberwise equivalent factors are equivalent. *)
Definition cate_prod_0gpd {I J : Type} (ie : I <~> J)
  (G : I -> ZeroGpd) (H : J -> ZeroGpd)
  (f : forall (i : I), G i $<~> H (ie i))
  : prod_0gpd I G $<~> prod_0gpd J H.
Proof.
  snapply cate_adjointify.
  - snapply Build_Fun01.
    + intros h j.
      exact (transport H (eisretr ie j) (cate_fun (f (ie^-1 j)) (h _))).
    + napply Build_Is0Functor.
      intros g h p j.
      destruct (eisretr ie j).
      refine (_ $o Hom_path (transport_1 _ _)).
      apply Build_Fun01.
      exact (p _).
  - exact (equiv_prod_0gpd_corec (fun i => (f i)^-1$ $o prod_0gpd_pr (ie i))).
  - intros h j.
    cbn.
    destruct (eisretr ie j).
    exact (cate_isretr (f _) _).
  - intros g i.
    cbn.
    refine (_ $o Hom_path
            (ap (cate_fun (f i)^-1$) (transport2 _ (eisadj ie i) _))).
    destruct (eissect ie i).
    exact (cate_issect (f _) _).
Defined.
