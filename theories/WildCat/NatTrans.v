Require Import Basics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Square.

(** ** Natural transformations *)

Definition Transformation {A B : Type} `{IsGraph B} (F : A -> B) (G : A -> B)
  := forall (a : A), F a $-> G a.

Notation "F $=> G" := (Transformation F G).

(** A 1-natural transformation is natural up to a 2-cell, so its codomain must be a 1-category. *)
Class Is1Natural {A B : Type} `{IsGraph A} `{Is1Cat B}
      (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
      (alpha : F $=> G) :=
  isnat : forall a a' (f : a $-> a'),
     (alpha a') $o (fmap F f) $== (fmap G f) $o (alpha a).

Arguments Is1Natural {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B}
  F {is0functor_F} G {is0functor_G} alpha : rename.
Arguments isnat {_ _ _ _ _ _ _ _ _ _ _} alpha {alnat _ _} f : rename.

Record NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} (F G : A -> B)
  {ff : Is0Functor F} {fg : Is0Functor G} :=
{
  trans_nattrans : F $=> G ;
  is1natural_nattrans : Is1Natural F G trans_nattrans ;
}.

Global Existing Instance is1natural_nattrans.
Coercion trans_nattrans : NatTrans >-> Transformation.

(** The transposed natural square *)
Definition isnat_tr {A B : Type} `{IsGraph A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      (alpha : F $=> G) `{!Is1Natural F G alpha}
      {a a' : A} (f : a $-> a')
  : (fmap G f) $o (alpha a) $== (alpha a') $o (fmap F f)
  := (isnat alpha f)^$.

Definition id_transformation {A B : Type} `{Is01Cat B} (F : A -> B)
  : F $=> F
  := fun a => Id (F a).

Global Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
       (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (id_transformation F).
Proof.
  intros a b f; cbn.
  refine (cat_idl _ $@ (cat_idr _)^$).
Defined.

Definition nattrans_id {A B : Type} (F : A -> B)
  `{IsGraph A, Is1Cat B, !Is0Functor F}
  : NatTrans F F.
Proof.
  nrapply Build_NatTrans.
  rapply is1natural_id.
Defined.

Definition trans_comp {A B : Type} `{Is01Cat B}
           {F G K : A -> B} (gamma : G $=> K) (alpha : F $=> G)
  : F $=> K
  := fun a => gamma a $o alpha a.

Definition trans_prewhisker {A B C : Type} {F G : B -> C}
  `{Is01Cat B, Is01Cat C} (gamma : F $=> G) (K : A -> B) 
  : F o K $=> G o K
  := gamma o K.

Definition trans_postwhisker {A B C : Type} {F G : A -> B}
  (K : B -> C) `{Is01Cat B, Is01Cat C, !Is0Functor K} (gamma : F $=> G)
  : K o F $=> K o G
  := fun a => fmap K (gamma a).

Global Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
       {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
       (gamma : G $=> K) `{!Is1Natural G K gamma}
       (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (trans_comp gamma alpha).
Proof.
  intros a b f; unfold trans_comp; cbn.
  refine (cat_assoc _ _ _ $@ (_ $@L isnat alpha f) $@ _).
  refine (cat_assoc_opp _ _ _ $@ (isnat gamma f $@R _) $@ _).
  apply cat_assoc.
Defined.

Global Instance is1natural_prewhisker {A B C : Type} {F G : B -> C} (K : A -> B)
  `{IsGraph A, Is01Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (F o K) (G o K) (trans_prewhisker gamma K).
Proof.
  intros x y f; unfold trans_prewhisker; cbn.
  exact (L _ _ _).
Defined.

Global Instance is1natural_postwhisker {A B C : Type} {F G : A -> B} (K : B -> C)
 `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G, !Is0Functor K, !Is1Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (K o F) (K o G) (trans_postwhisker K gamma).
Proof.
  intros x y f; unfold trans_postwhisker; cbn.
  refine (_^$ $@ _ $@ _).
  1,3: rapply fmap_comp.
  rapply fmap2.
  exact (L _ _ _).
Defined.

Definition nattrans_comp {A B : Type} {F G K : A -> B}
  `{IsGraph A, Is1Cat B, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatTrans G K -> NatTrans F G -> NatTrans F K.
Proof.
  intros alpha beta.
  nrapply Build_NatTrans.
  rapply (is1natural_comp alpha beta).
Defined.

Definition nattrans_prewhisker {A B C : Type} {F G : B -> C}
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G}
  (alpha : NatTrans F G) (K : A -> B) `{!Is0Functor K} 
  : NatTrans (F o K) (G o K).
Proof.
  nrapply Build_NatTrans.
  rapply (is1natural_prewhisker K alpha).
Defined.

Definition nattrans_postwhisker {A B C : Type} {F G : A -> B} (K : B -> C)
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G,
    !Is0Functor K, !Is1Functor K} 
  : NatTrans F G -> NatTrans (K o F) (K o G).
Proof.
  intros alpha.
  nrapply Build_NatTrans.
  rapply (is1natural_postwhisker K alpha).
Defined.

(** Modifying a transformation to something pointwise equal preserves naturality. *)
Definition is1natural_homotopic {A B : Type} `{Is01Cat A} `{Is1Cat B}
      {F : A -> B} `{!Is0Functor F} {G : A -> B} `{!Is0Functor G}
      {alpha : F $=> G} (gamma : F $=> G) `{!Is1Natural F G gamma}
      (p : forall a, alpha a $== gamma a)
  : Is1Natural F G alpha.
Proof.
  intros a b f.
  exact ((p b $@R _) $@ isnat gamma f $@ (_ $@L (p a)^$)).
Defined.

(** Natural equivalences *)

Record NatEquiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  (F G : A -> B) `{!Is0Functor F, !Is0Functor G} :=
{
  cat_equiv_natequiv : forall a, F a $<~> G a ;
  is1natural_natequiv : Is1Natural F G (fun a => cat_equiv_natequiv a) ;
}.

Arguments NatEquiv {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B} {hasequivs_B}
  F G {is0functor_F} {is0functor_G} : rename.
Arguments Build_NatEquiv {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B} {hasequivs_B}
  F G {is0functor_F} {is0functor_G} e isnat_e: rename.

Global Existing Instance is1natural_natequiv.
Coercion cat_equiv_natequiv : NatEquiv >-> Funclass.

Coercion nattrans_natequiv {A B : Type} `{IsGraph A} `{HasEquivs B}
  (F G : A -> B) `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatTrans F G.
Proof.
  intros alpha.
  nrapply Build_NatTrans.
  rapply (is1natural_natequiv _ _ alpha).
Defined.

Definition natequiv_compose {A B} {F G H : A -> B} `{IsGraph A} `{HasEquivs B}
  `{!Is0Functor F, !Is0Functor G, !Is0Functor H}
  : NatEquiv G H -> NatEquiv F G -> NatEquiv F H.
Proof.
  intros alpha beta.
  snrapply Build_NatEquiv.
  1: exact (fun a => alpha a $oE beta a).
  hnf; intros x y f.
  refine (cat_prewhisker (compose_cate_fun _ _) _ $@ _).
  refine (_ $@ cat_postwhisker _ (compose_cate_fun _ _)^$).
  revert x y f.
  rapply is1natural_comp.
Defined.

Definition natequiv_prewhisker {A B C} {H K : B -> C}
  `{IsGraph A, HasEquivs B, HasEquivs C, !Is0Functor H, !Is0Functor K}
  (alpha : NatEquiv H K) (F : A -> B) `{!Is0Functor F}
  : NatEquiv (H o F) (K o F).
Proof.
  snrapply Build_NatEquiv.
  1: exact (alpha o F).
  exact (is1natural_prewhisker _ _).
Defined.

Definition natequiv_postwhisker {A B C} {F G : A -> B}
  `{IsGraph A, HasEquivs B, HasEquivs C, !Is0Functor F, !Is0Functor G}
   (K : B -> C) (alpha : NatEquiv F G) `{!Is0Functor K, !Is1Functor K}
  : NatEquiv (K o F) (K o G).
Proof.
  snrapply Build_NatEquiv.
  1: exact (fun a => emap K (alpha a)).
  hnf. intros x y f.
  refine (cat_prewhisker (cate_buildequiv_fun _) _ $@ _).
  refine (_ $@ cat_postwhisker _ (cate_buildequiv_fun _)^$).
  revert x y f.
  exact (is1natural_postwhisker _ _).
Defined.

Definition natequiv_inverse {A B : Type} `{IsGraph A} `{HasEquivs B}
  (F G : A -> B) `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv G F.
Proof.
  intros [alpha I].
  snrapply Build_NatEquiv.
  1: intro a; symmetry; apply alpha.
  intros X Y f.
  apply vinverse, I.
Defined.

(** This lemma might seem unnecessery since as functions ((F o G) o K) and (F o (G o K)) are definitionally equal. But the functor instances of both sides are different. This can be a nasty trap since you cannot see this difference clearly. *)
Definition natequiv_functor_assoc_ff_f {A B C D : Type}
  `{IsGraph A, HasEquivs B, HasEquivs C, HasEquivs D} (** These are a lot of instances... *)
  (F : C -> D) (G : B -> C) (K : A -> B) `{!Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatEquiv ((F o G) o K) (F o (G o K)).
Proof.
  snrapply Build_NatEquiv.
  1: intro; reflexivity.
  intros X Y f.
  refine (cat_prewhisker (id_cate_fun _) _ $@ cat_idl _ $@ _^$).
  refine (cat_postwhisker _ (id_cate_fun _) $@ cat_idr _).
Defined.
