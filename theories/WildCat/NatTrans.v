Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Square.
Require Import WildCat.Opposite.

(** * Wild Natural Transformations *)

(** ** Transformations *)

(** *** Definition *)

(** A transformation is simply a family of 1-cells over some base type [A] between the sections of two dependent functions [F] and [G]. In most cases [F] and [G] will be non-dependent functors. *)
Definition Transformation {A : Type} {B : A -> Type} `{forall x, IsGraph (B x)}
  (F G : forall (x : A), B x)
  := forall (a : A), F a $-> G a.

(** This lets us apply transformations to things. Identity Coercion tells Coq that this coercion is in fact definitionally the identity map so it doesn't need to insert it, but merely rewrite definitionally when typechecking. *)
Identity Coercion fun_trans : Transformation >-> Funclass.

Notation "F $=> G" := (Transformation F G).

(** The identity transformation between a functor and itself is the identity function at the section. *)
Definition trans_id {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F
  := fun a => Id (F a).

(** Transformations can be composed pointwise. *)
Definition trans_comp {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K
  := fun a => gamma a $o alpha a.

(** Transformations can be prewhiskered by a function. This means we precompose both sides of the transformation with a function. *)
Definition trans_prewhisker {A B : Type} {C : B -> Type} {F G : forall x, C x}
  `{Is01Cat B} `{!forall x, IsGraph (C x)}
  `{!forall x, Is01Cat (C x)} (gamma : F $=> G) (K : A -> B) 
  : F o K $=> G o K
  := gamma o K.

(** Transformations can be postwhiskered by a function. This means we postcompose both sides of the transformation with a function. *)
Definition trans_postwhisker {A B C : Type} {F G : A -> B}
  (K : B -> C) `{Is01Cat B, Is01Cat C, !Is0Functor K} (gamma : F $=> G)
  : K o F $=> K o G
  := fun a => fmap K (gamma a).

(** A transformation in the opposite category is simply a transformation in the original category with the direction swapped. *)
Definition trans_op {A} {B} `{Is01Cat B}
  (F : A -> B) (G : A -> B) (alpha : F $=> G)
  : Transformation (A:=A^op) (B:=fun _ => B^op) G (F : A^op -> B^op)
  := alpha.

(** ** Naturality *)

(** A transformation is 1-natural if there exists a 2-cell witnessing the naturality square. The codomain of the transformation must be a wild 1-category. *)
Class Is1Natural {A B : Type} `{IsGraph A, Is1Cat B}
  (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
  (alpha : F $=> G) := Build_Is1Natural' {
  isnat {a a'} (f : a $-> a') : alpha a' $o fmap F f $== fmap G f $o alpha a;
  (** We also include the transposed naturality square in the definition so that opposite natural transformations are definitionally involutive. In most cases, this will be constructed to be the inverse of the [isnat] field. *)
  isnat_tr {a a'} (f : a $-> a') : fmap G f $o alpha a $== alpha a' $o fmap F f;
}.

Arguments Is1Natural {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B}
  F {is0functor_F} G {is0functor_G} alpha : rename.
Arguments isnat {_ _ _ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.
Arguments isnat_tr {_ _ _ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

(** We coerce naturality proofs to their naturality square as the [isnat] projection can be unwieldy in certain situations where the transformation is difficult to write down. This allows for the naturality proof to be used directly. *)
Coercion isnat : Is1Natural >-> Funclass.

Definition Build_Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G} (alpha : F $=> G)
  (isnat : forall a a' (f : a $-> a'), alpha a' $o fmap F f $== fmap G f $o alpha a)
  : Is1Natural F G alpha.
Proof.
  snapply Build_Is1Natural'.
  - exact isnat.
  - intros a a' f.
    exact (isnat a a' f)^$.
Defined.

(** The identity transformation is 1-natural. *)
Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (trans_id F).
Proof.
  snapply Build_Is1Natural.
  intros a b f; cbn.
  exact (cat_idl _ $@ (cat_idr _)^$).
Defined.

(** The composite of 1-natural transformations is 1-natural. *)
Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
  {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
  (gamma : G $=> K) `{!Is1Natural G K gamma}
  (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (trans_comp gamma alpha).
Proof.
  snapply Build_Is1Natural.
  intros a b f; unfold trans_comp; cbn.
  refine (cat_assoc _ _ _ $@ (_ $@L isnat alpha f) $@ _).
  refine (cat_assoc_opp _ _ _ $@ (isnat gamma f $@R _) $@ _).
  apply cat_assoc.
Defined.

(** Prewhiskering a transformation preserves naturality. *)
Instance is1natural_prewhisker {A B C : Type} {F G : B -> C} (K : A -> B)
  `{IsGraph A, Is01Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (F o K) (G o K) (trans_prewhisker gamma K).
Proof.
  snapply Build_Is1Natural.
  intros x y f; unfold trans_prewhisker; cbn.
  exact (isnat gamma _).
Defined.

(** Postwhiskering a transformation preserves naturality. *)
Instance is1natural_postwhisker {A B C : Type} {F G : A -> B} (K : B -> C)
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G,
    !Is0Functor K, !Is1Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (K o F) (K o G) (trans_postwhisker K gamma).
Proof.
  snapply Build_Is1Natural.
  intros x y f; unfold trans_postwhisker; cbn.
  refine (_^$ $@ _ $@ _).
  1,3: rapply fmap_comp.
  rapply fmap2.
  exact (isnat gamma _).
Defined.

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is01Cat A} `{Is1Cat B}
  {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
  {alpha : F $=> G} (gamma : F $=> G) `{!Is1Natural F G gamma}
  (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  snapply Build_Is1Natural.
  intros a b f.
  exact ((p b $@R _) $@ isnat gamma f $@ (_ $@L (p a)^$)).
Defined.

(** The opposite of a natural transformation is natural. *)
Instance is1natural_op A B `{Is01Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
  (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural (G : A^op -> B^op) (F : A^op -> B^op) (trans_op F G alpha).
Proof.
  unfold op.
  snapply Build_Is1Natural'.
  - intros a b.
    exact (isnat_tr alpha).
  - intros a b.
    exact (isnat alpha).
Defined.

(** ** Natural transformations *)

(** Here we give the bundled definition of a natural transformation which can be more convenient to work with in certain situations. It forms the Hom type of the functor category. *)

Record NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} {F G : A -> B}
  {ff : Is0Functor F} {fg : Is0Functor G} := {
  #[reversible=no]
  trans_nattrans :> F $=> G;
  is1natural_nattrans :: Is1Natural F G trans_nattrans;
}.

Arguments NatTrans {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B}
  F G {is0functor_F} {is0functor_G} : rename.
Arguments Build_NatTrans {A B isgraph_A isgraph_B is2graph_B is01cat_B is1cat_B
  F G is0functor_F is0functor_G} alpha isnat_alpha : rename.

Definition issig_NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} (F G : A -> B)
  {ff : Is0Functor F} {fg : Is0Functor G}
  : _ <~> NatTrans F G := ltac:(issig).

Definition nattrans_id {A B : Type} (F : A -> B)
  `{IsGraph A, Is1Cat B, !Is0Functor F}
  : NatTrans F F
  := Build_NatTrans (trans_id F) _.

Definition nattrans_comp {A B : Type} {F G K : A -> B}
  `{IsGraph A, Is1Cat B, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatTrans G K -> NatTrans F G -> NatTrans F K
  := fun alpha beta => Build_NatTrans (trans_comp alpha beta) _.

Definition nattrans_prewhisker {A B C : Type} {F G : B -> C}
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G}
  (alpha : NatTrans F G) (K : A -> B) `{!Is0Functor K} 
  : NatTrans (F o K) (G o K)
  := Build_NatTrans (trans_prewhisker alpha K) _.

Definition nattrans_postwhisker {A B C : Type} {F G : A -> B} (K : B -> C)
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G,
    !Is0Functor K, !Is1Functor K} 
  : NatTrans F G -> NatTrans (K o F) (K o G)
  := fun alpha => Build_NatTrans (trans_postwhisker K alpha) _.

Definition nattrans_op {A B : Type} `{Is01Cat A} `{Is1Cat B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatTrans F G
    -> NatTrans (A:=A^op) (B:=B^op) (G : A^op -> B^op) (F : A^op -> B^op)
  := fun alpha => Build_NatTrans (trans_op F G alpha) _.

(** ** Natural equivalences *)

(** Natural equivalences are families of equivalences that are natural. *)
Record NatEquiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G} := {
  #[reversible=no]
  cat_equiv_natequiv :> forall a, F a $<~> G a ;
  is1natural_natequiv :: Is1Natural F G (fun a => cat_equiv_natequiv a) ;
}.

Arguments NatEquiv {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B} {hasequivs_B}
  F G {is0functor_F} {is0functor_G} : rename.
Arguments Build_NatEquiv {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B} {hasequivs_B}
  F G {is0functor_F} {is0functor_G} e isnat_e: rename.

Definition issig_NatEquiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  (F G : A -> B) `{!Is0Functor F, !Is0Functor G}
  : _ <~> NatEquiv F G := ltac:(issig).

(** From a given natural equivalence, we can get the underlying natural transformation. *)
Lemma nattrans_natequiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatTrans F G.
Proof.
  intros alpha.
  napply Build_NatTrans.
  exact (is1natural_natequiv alpha).
Defined.

(** Throws a warning, but can probably be ignored. *)
Global Set Warnings "-ambiguous-paths".
Coercion nattrans_natequiv : NatEquiv >-> NatTrans.

(** The above coercion sometimes doesn't trigger when it should, so we add the following. *)
Definition isnat_natequiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G} (alpha : NatEquiv F G)
  {a a' : A} (f : a $-> a')
  := isnat (nattrans_natequiv alpha) f.

(** Often we wish to build a natural equivalence from a natural transformation and a pointwise proof that it is an equivalence. *)
Definition Build_NatEquiv' {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  (alpha : NatTrans F G) `{forall a, CatIsEquiv (alpha a)}
  : NatEquiv F G.
Proof.
  snapply Build_NatEquiv.
  - intro a.
    exact (Build_CatEquiv (alpha a)).
  - snapply Build_Is1Natural'.
    + intros a a' f.
      refine ((cate_buildequiv_fun _ $@R _) $@ _ $@ (_ $@L cate_buildequiv_fun _)^$).
      exact (isnat alpha _).
    + intros a a' f.
      refine ((_ $@L cate_buildequiv_fun _) $@ _ $@ (cate_buildequiv_fun _ $@R _)^$).
      exact (isnat_tr alpha _).
Defined.

Definition natequiv_id {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F : A -> B} `{!Is0Functor F}
  : NatEquiv F F
  := Build_NatEquiv' (nattrans_id F).

Definition natequiv_compose {A B} {F G H : A -> B} `{IsGraph A} `{HasEquivs B}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor H}
  (alpha : NatEquiv G H) (beta : NatEquiv F G)
  : NatEquiv F H
  := Build_NatEquiv' (nattrans_comp alpha beta).

Definition natequiv_prewhisker {A B C} {H K : B -> C}
  `{IsGraph A, HasEquivs B, HasEquivs C, !Is0Functor H, !Is0Functor K}
  (alpha : NatEquiv H K) (F : A -> B) `{!Is0Functor F}
  : NatEquiv (H o F) (K o F)
  := Build_NatEquiv' (nattrans_prewhisker alpha F).

Definition natequiv_postwhisker {A B C} {F G : A -> B}
  `{IsGraph A, HasEquivs B, HasEquivs C, !Is0Functor F, !Is0Functor G}
   (K : B -> C) (alpha : NatEquiv F G) `{!Is0Functor K, !Is1Functor K}
  : NatEquiv (K o F) (K o G).
Proof.
  srefine (Build_NatEquiv' (nattrans_postwhisker K alpha)).
  2: unfold nattrans_postwhisker, trans_postwhisker; cbn.
  all: exact _.
Defined.

Lemma natequiv_op {A B : Type} `{Is01Cat A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv (G : A^op -> B^op) F.
Proof.
  intros [a n].
  snapply Build_NatEquiv.
  1: exact a.
  by rapply is1natural_op.
Defined.

(** We can form the inverse natural equivalence by inverting each map in the family. The naturality proof follows from standard lemmas about inverses. *)
Definition natequiv_inverse {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv G F.
Proof.
  intros [alpha I].
  snapply Build_NatEquiv.
  1: exact (fun a => (alpha a)^-1$).
  snapply Build_Is1Natural'.
  + intros X Y f.
    apply vinverse, I.
  + intros X Y f.
    apply hinverse, I.
Defined.

(** This lemma might seem unnecessary since as functions ((F o G) o K) and (F o (G o K)) are definitionally equal. But the functor instances of both sides are different. This can be a nasty trap since you cannot see this difference clearly. *)
Definition natequiv_functor_assoc_ff_f {A B C D : Type}
  `{IsGraph A, HasEquivs B, HasEquivs C, HasEquivs D} 
  (F : C -> D) (G : B -> C) (K : A -> B)
  `{!Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatEquiv ((F o G) o K) (F o (G o K)).
Proof.
  snapply Build_NatEquiv.
  1: intro; reflexivity.
  snapply Build_Is1Natural.
  intros X Y f.
  refine (cat_prewhisker (id_cate_fun _) _ $@ cat_idl _ $@ _^$).
  exact (cat_postwhisker _ (id_cate_fun _) $@ cat_idr _).
Defined.

(** ** Pointed natural transformations *)

Definition PointedTransformation {B C : Type} `{Is1Cat B, Is1Gpd C}
  `{IsPointed B, IsPointed C} (F G : B -->* C)
  := {eta : F $=> G & eta (point _) $== bp_pointed F $@ (bp_pointed G)^$}.

Notation "F $=>* G" := (PointedTransformation F G) (at level 70).

Definition ptransformation_inverse {B C : Type} `{Is1Cat B, Is1Gpd C}
  `{IsPointed B, IsPointed C} (F G : B -->* C)
  : (F $=>* G) -> (G $=>* F).
Proof.
intros [h p].
  exists (fun x => (h x)^$).
  refine (gpd_rev2 p $@ _).
  refine (gpd_rev_pp _ _ $@ _).
  refine (_ $@L _).
  apply gpd_rev_rev.
Defined.

Notation "h ^*$" := (ptransformation_inverse _ _ h) (at level 5).

Definition ptransformation_compose {B C : Type} `{Is1Cat B, Is1Gpd C}
  `{IsPointed B, IsPointed C} {F0 F1 F2 : B -->* C}
  : (F0 $=>* F1) -> (F1 $=>* F2) -> (F0 $=>* F2).
Proof.
  intros [h0 p0] [h1 p1].
  exists (trans_comp h1 h0).
  refine ((p1 $@R _) $@ (_ $@L p0) $@ _);
    unfold gpd_comp; cbn.
  refine (cat_assoc _ _ _ $@ _).
  rapply (fmap _).
  apply gpd_h_Vh.
Defined.

Notation "h $@* k" := (ptransformation_compose h k) (at level 40).

(* TODO: *)
(* Morphisms of natural transformations - Modifications *)
(* Since [Transformation] is dependent, we can define a modification to be a transformation together with a cylinder condition. This doesn't seem to be too useful as of yet however. We would also need better ways to write down cylinders. *)

