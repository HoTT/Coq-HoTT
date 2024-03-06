Require Import Basics.Overture Basics.Tactics Basics.Equivalences
               Basics.PathGroupoids.
Require Import WildCat.Core WildCat.Equiv WildCat.EquivGpd WildCat.Prod
               WildCat.Forall.

(** * The wild 1-category of 0-groupoids. *)

(** Here we define a wild 1-category structure on the type of 0-groupoids.  We think of the 1-cells [g $== h] in a 0-groupoid [G] as a substitute for the paths [g = h], and so we closely follow the definitions used for the 1-category of types with [=] replaced by [$==].  In fact, the 1-category structure on types should be the pullback of the 1-category structure on 0-groupoids along a natural map [Type -> ZeroGpd] which sends [A] to [A] equipped with its path types.  A second motivating example is the 0-groupoid with underlying type [A -> B] and homotopies as the 1-cells.  The definitions chosen here exactly make the Yoneda lemma [opyon_equiv_0gpd] go through. *)

Record ZeroGpd := {
  carrier :> Type;
  isgraph_carrier : IsGraph carrier;
  is01cat_carrier : Is01Cat carrier;
  is0gpd_carrier : Is0Gpd carrier;
}.

Global Existing Instance isgraph_carrier.
Global Existing Instance is01cat_carrier.
Global Existing Instance is0gpd_carrier.

(* The morphisms of 0-groupoids are the 0-functors.  This is the same as [Fun01], but we put a different graph and 01-category structure on it, so we give this a custom name. *)
Record Morphism_0Gpd (G H : ZeroGpd) := {
  fun_0gpd :> carrier G -> carrier H;
  is0functor_fun_0gpd : Is0Functor fun_0gpd;
}.

Global Existing Instance is0functor_fun_0gpd.

(** Now we show that the type [ZeroGpd] of 0-groupoids is itself a 1-category, with morphisms the 0-functors. *)
Global Instance isgraph_0gpd : IsGraph ZeroGpd.
Proof.
  apply Build_IsGraph.
  exact Morphism_0Gpd.
Defined.

Global Instance is01cat_0gpd : Is01Cat ZeroGpd.
Proof.
  srapply Build_Is01Cat.
  - intro G.
    exact (Build_Morphism_0Gpd G G idmap _).
  - intros G H K f g.
    exact (Build_Morphism_0Gpd _ _ (f o g) _).
Defined.

(* The 2-cells are unnatural transformations, and are analogous to homotopies. *)
Global Instance is2graph_0gpd : Is2Graph ZeroGpd.
Proof.
  intros G H.
  snrapply Build_IsGraph.
  intros f g.
  exact (forall x : G, f x $== g x).
Defined.

Global Instance is1cat_0gpd : Is1Cat ZeroGpd.
Proof.
  snrapply Build_Is1Cat.
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
  - reflexivity. (* Left identity. *)
  - reflexivity. (* Right identity. *)
Defined.

(** We define equivalences of 0-groupoids as the bi-invertible maps, using [Cat_BiInv] and [Cat_IsBiInv].  This definition is chosen to provide what is needed for the Yoneda lemma, and because it specializes to one of the correct definitions for types. *)

Global Instance hasequivs_0gpd : HasEquivs ZeroGpd
  := cat_hasequivs ZeroGpd.

(** Coq can't find the composite of the coercions [cate_fun : G $<~> H >-> G $-> H] and [fun_0gpd : Morphism_0Gpd G H >-> G -> H], probably because it passes through the definitional equality of [G $-> H] and [Morphism_0Gpd G H].  I couldn't find a solution, so instead here is a helper function to manually do the coercion when needed. *)

Definition equiv_fun_0gpd {G H : ZeroGpd} (f : G $<~> H) : G -> H
  := fun_0gpd _ _ (cat_equiv_fun _ _ _ f).

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
Global Instance issurjinj_equiv_0gpd {G H : ZeroGpd} (f : G $<~> H)
  : IsSurjInj (equiv_fun_0gpd f).
Proof.
  econstructor.
  - intro y.
    exists (equiv_fun_0gpd f^-1$ y).
    rapply cat_eisretr.
  - apply isinj_equiv_0gpd.
Defined.

(** Conversely, every injective split essentially surjective 0-functor is an equivalence.  In practice, this is often the easiest way to prove that a functor is an equivalence. *)
Definition isequiv_0gpd_issurjinj {G H : ZeroGpd} (F : G $-> H)
  {e : IsSurjInj F}
  : Cat_IsBiInv F.
Proof.
  destruct e as [e0 e1]; unfold SplEssSurj in e0.
  srapply catie_adjointify.
  - snrapply Build_Morphism_0Gpd.
    1: exact (fun y => (e0 y).1).
    snrapply Build_Is0Functor; cbn beta.
    intros y1 y2 m.
    apply e1.
    exact ((e0 y1).2 $@ m $@ ((e0 y2).2)^$).
  - cbn.  apply e0.
  - cbn.  intro x.
    apply e1.
    apply e0.
Defined.

Definition prod_0gpd (I : Type) (G : I -> ZeroGpd) : ZeroGpd.
Proof.
  rapply (Build_ZeroGpd (forall i, G i)).
Defined.

Definition prod_0gpd_pr {I : Type} {G : I -> ZeroGpd}
  : forall i, prod_0gpd I G $-> G i.
Proof.
  intros i.
  snrapply Build_Morphism_0Gpd.
  1: exact (fun f => f i).
  snrapply Build_Is0Functor; cbn beta.
  intros f g p.
  exact (p i).
Defined.

(** The universal property of the product of 0-groupoids holds almost definitionally. *)
Definition equiv_prod_0gpd_corec {I : Type} {G : ZeroGpd} {H : I -> ZeroGpd}
  : (forall i, G $-> H i) <~> (G $-> prod_0gpd I H).
Proof.
  snrapply Build_Equiv.
  { intro f.
    snrapply Build_Morphism_0Gpd.
    1: exact (fun x i => f i x).
    snrapply Build_Is0Functor; cbn beta.
    intros x y p i; simpl.
    exact (fmap (f i) p). }
  snrapply Build_IsEquiv.
  - intro f.
    intros i.
    exact (prod_0gpd_pr i $o f).
  - intro f.
    reflexivity.
  - intro f.
    reflexivity.
  - reflexivity.
Defined.

Definition cate_prod_0gpd {I J : Type} (ie : I <~> J)
  (G : I -> ZeroGpd) (H : J -> ZeroGpd)
  (f : forall (i : I), G i $<~> H (ie i))
  : prod_0gpd I G $<~> prod_0gpd J H.
Proof.
  snrapply cate_adjointify.
  - snrapply Build_Morphism_0Gpd.
    + intros h j.
      exact (transport H (eisretr ie j) (cate_fun (f (ie^-1 j)) (h _))).
    + nrapply Build_Is0Functor.
      intros g h p j.
      destruct (eisretr ie j).
      refine (_ $o Hom_path (transport_1 _ _)).
      apply Build_Morphism_0Gpd.
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
