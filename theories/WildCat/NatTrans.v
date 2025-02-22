Require Import Basics.Overture Basics.Tactics.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Square.
Require Import WildCat.Opposite.
Require Import WildCat.Induced.

(** We begin by introducing graph homomorphisms and
    some operations on them.
*)
Record Fun01 (A B : Type) `{IsGraph A} `{IsGraph B} := {
  fun01_F : A -> B;
  fun01_is0functor : Is0Functor fun01_F;
}.

Arguments fun01_F {A B H H0}.
Coercion fun01_F : Fun01 >-> Funclass.
Global Existing Instance fun01_is0functor.

Arguments Build_Fun01 A B {isgraph_A isgraph_B} F {fun01_is0functor} : rename.

Definition issig_Fun01 (A B : Type) `{IsGraph A} `{IsGraph B}
  : _  <~> Fun01 A B := ltac:(issig).

(* * There is a graph whose nodes are graphs and whose edges are graph homomorphisms.
Module Gph_Hom.
  Record type (G H : Graph) := {
    F0 : G -> H;
    fmap : Is0Functor F0
  }.
End Gph_Hom.
Arguments Gph_Hom.F0 {G H}.
Notation Gph_Hom := Gph_Hom.type.
Coercion Gph_Hom.F0 : Gph_Hom >-> Funclass.
#[reversible] Coercion Gph_Hom.fmap : Gph_Hom >-> Is0Functor.
Existing Instance Gph_Hom.fmap.
 *)

Instance is0Graph_Graph : IsGraph Graph := {
  Hom A B := Fun01 A B
}.

(** There is a category of graphs under composition. *)
Instance is01cat_Graph : Is01Cat Graph := { 
    Id A := {| fun01_F := idmap; fun01_is0functor := _ |}; 
    cat_comp A B C G F :=
     {| fun01_F := compose G F ; fun01_is0functor := _ |} }.

(** ** Transformations *)

(** *** Definition *)

(** A transformation is simply a family of 1-cells over some base type [A] between the sections of two dependent functions [F] and [G]. In most cases [F] and [G] will be non-dependent functors. *)
Definition Transformation {A : Type} {B : A -> Type} `{forall x, IsGraph (B x)}
  (F G : forall (x : A), B x)
  := forall (a : A), F a $-> G a.

(** This lets us apply transformations to things. Identity Coercion tells coq that this coercion is in fact definitionally the identity map so it doesn't need to insert it, but merely rewrite definitionally when typechecking. *)
Identity Coercion fun_trans : Transformation >-> Funclass.

Instance Is2GraphGraph : Is2Graph Graph := 
  fun A B => {| Hom F G := Transformation (fun01_F F) (fun01_F G)|}.

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


(** Bundled opposite functors *)
Definition fun01_op (A B : Type) `{IsGraph A} `{IsGraph B}
  : Fun01 A B -> Fun01 A^op B^op.
Proof.
  intros F.
  rapply (Build_Fun01 A^op B^op F).
Defined.


(* Module Functor.
  Class class (A B : Category) (F : A -> B) := {
    is0functor : Is0Functor F;
    is1functor : Is1Functor F
  }.
  Record type (A B : Category) := {
    fmap : A -> B;
    class_of : class A B fmap
  }.
End Functor.
Arguments Functor.fmap {A B}.
Coercion Functor.fmap : Functor.type >-> Funclass.
Existing Instance Functor.class_of.
Existing Instance Functor.is0functor.
Existing Instance Functor.is1functor.
Notation Functor := Functor.type. *)

(** ** Categories of 1-coherent 1-functors *)

(* Note that even if [A] and [B] are fully coherent oo-categories, the objects of our "functor category" are not fully coherent.  Thus we cannot in general expect this "functor category" to itself be fully coherent.  However, it is at least a 0-coherent 1-category, as long as [B] is a 1-coherent 1-category. *)

Record Fun11 (A B : Type) `{Is1Cat A} `{Is1Cat B} :=
{
  fun11_fun : A -> B ;
  is0functor_fun11 : Is0Functor fun11_fun ;
  is1functor_fun11 : Is1Functor fun11_fun
}.

Coercion fun11_fun : Fun11 >-> Funclass.
Global Existing Instance is0functor_fun11.
Global Existing Instance is1functor_fun11.

Arguments Build_Fun11 A B
  {isgraph_A is2graph_A is01cat_A is1cat_A
   isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_fun11 is1functor_fun11} : rename.

Coercion fun01_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : Fun11 A B)
: Fun01 A B.
Proof.
exists F; exact _.
Defined.

Instance IsGraphCat : IsGraph Category := { Hom F G := Fun11 F G }.

(** * Identity functors *)

Definition fun01_id {A} `{IsGraph A} : Fun01 A A
  := Build_Fun01 A A idmap.

Print Implicit Build_Fun11.
Definition fun11_id {A} `{Is1Cat A} : Fun11 A A
  := Build_Fun11 _ _ idmap.

(* Definition functor_id {A : Category} : Functor A A := 
{| Functor.fmap := idmap;
   Functor.class_of := 
   {| Functor.is0functor := _ ; 
      Functor.is1functor := _|}
|}.

Definition functor_compose {A B C : Category} (G : B $-> C) (F : A $-> B) 
  : Functor A C  := {|
    Functor.fmap := compose G F;
    Functor.class_of := {|
      Functor.is0functor := _;
      Functor.is1functor := _
  |}
|}. *)

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
  snrapply Build_Is1Natural'.
  - exact isnat.
  - intros a a' f.
    exact (isnat a a' f)^$.
Defined.

(** The identity transformation is 1-natural. *)
Global Instance is1natural_id {A B : Type} `{IsGraph A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F}
  : Is1Natural F F (trans_id F).
Proof.
  snrapply Build_Is1Natural.
  intros a b f; cbn.
  refine (cat_idl _ $@ (cat_idr _)^$).
Defined.

(** The composite of 1-natural transformations is 1-natural. *)
Global Instance is1natural_comp {A B : Type} `{IsGraph A} `{Is1Cat B}
  {F G K : A -> B} `{!Is0Functor F} `{!Is0Functor G} `{!Is0Functor K}
  (gamma : G $=> K) `{!Is1Natural G K gamma}
  (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural F K (trans_comp gamma alpha).
Proof.
  snrapply Build_Is1Natural.
  intros a b f; unfold trans_comp; cbn.
  refine (cat_assoc _ _ _ $@ (_ $@L isnat alpha f) $@ _).
  refine (cat_assoc_opp _ _ _ $@ (isnat gamma f $@R _) $@ _).
  apply cat_assoc.
Defined.

(** Prewhiskering a transformation preserves naturality. *)
Global Instance is1natural_prewhisker {A B C : Type} {F G : B -> C} (K : A -> B)
  `{IsGraph A, Is01Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (F o K) (G o K) (trans_prewhisker gamma K).
Proof.
  snrapply Build_Is1Natural.
  intros x y f; unfold trans_prewhisker; cbn.
  exact (isnat gamma _).
Defined.

(** Postwhiskering a transformation preserves naturality. *)
Global Instance is1natural_postwhisker {A B C : Type} {F G : A -> B} (K : B -> C)
  `{IsGraph A, Is1Cat B, Is1Cat C, !Is0Functor F, !Is0Functor G,
    !Is0Functor K, !Is1Functor K}
  (gamma : F $=> G) `{L : !Is1Natural F G gamma}
  : Is1Natural (K o F) (K o G) (trans_postwhisker K gamma).
Proof.
  snrapply Build_Is1Natural.
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
  snrapply Build_Is1Natural.
  intros a b f.
  exact ((p b $@R _) $@ isnat gamma f $@ (_ $@L (p a)^$)).
Defined.

(** The opposite of a natural transformation is natural. *)
Global Instance is1natural_op A B `{Is01Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F} (G : A -> B) `{!Is0Functor G}
  (alpha : F $=> G) `{!Is1Natural F G alpha}
  : Is1Natural (G : A^op -> B^op) (F : A^op -> B^op) (trans_op F G alpha).
Proof.
  unfold op.
  snrapply Build_Is1Natural'.
  - intros a b.
    exact (isnat_tr alpha).
  - intros a b.
    exact (isnat alpha).
Defined.

(** ** Natural transformations *)

(** Here we give the bundled definition of a natural transformation which can be more convenient to work with in certain situations. It forms the Hom type of the functor category. *)

Record NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} (F G : A -> B)
  {ff : Is0Functor F} {fg : Is0Functor G} := {
  #[reversible=no]
  trans_nattrans :> F $=> G;
  is1natural_nattrans : Is1Natural F G trans_nattrans;
}.

Arguments NatTrans {A B} {isgraph_A}
  {isgraph_B} {is2graph_B} {is01cat_B} {is1cat_B}
  F G {is0functor_F} {is0functor_G} : rename.
Arguments Build_NatTrans {A B isgraph_A isgraph_B is2graph_B is01cat_B is1cat_B
  F G is0functor_F is0functor_G} alpha isnat_alpha : rename.
Arguments trans_nattrans {A B _ _ _ _ _ F G _ _}.
Global Existing Instance is1natural_nattrans.

Print Implicit trans_nattrans.

Definition issig_NatTrans {A B : Type} `{IsGraph A} `{Is1Cat B} (F G : A -> B)
  {ff : Is0Functor F} {fg : Is0Functor G}
  : _ <~> NatTrans F G := ltac:(issig).

  Global Instance isgraph_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : IsGraph (Fun01 A B).
  Proof.
    srapply Build_IsGraph.
    intros [F ?] [G ?].
    exact (NatTrans F G).
  Defined.

Global Instance isgraph_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
: IsGraph (Fun11 A B)
:= isgraph_induced fun01_fun11.

Instance Is2GraphCategory : Is2Graph Category := fun (A B : Category ) => {|
  Hom (F G : Fun11 A B) := NatTrans F G
|}.

Definition nattrans_id {A B : Type} (F : A -> B)
  `{IsGraph A, Is1Cat B, !Is0Functor F}
  : NatTrans F F
  := Build_NatTrans (trans_id F) _.

Definition nattrans_comp {A B : Type} {F G K : A -> B}
  `{IsGraph A, Is1Cat B, !Is0Functor F, !Is0Functor G, !Is0Functor K}
  : NatTrans G K -> NatTrans F G -> NatTrans F K
  := fun alpha beta => Build_NatTrans (trans_comp alpha beta) _.


Global Instance is01cat_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : Is01Cat (Fun01 A B).
  Proof.
    srapply Build_Is01Cat.
    - intros [F ?]; cbn.
      exact (nattrans_id F).
    - intros F G K gamma alpha; cbn in *.
      exact (nattrans_comp gamma alpha).
  Defined.


Global Instance is01cat_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : Is01Cat (Fun11 A B)
  := is01cat_induced fun01_fun11.


Global Instance is2graph_fun01 (A B : Type) `{IsGraph A, Is1Cat B}
  : Is2Graph (Fun01 A B).
Proof.
  intros [F ?] [G ?]; apply Build_IsGraph.
  intros [alpha ?] [gamma ?].
  exact (forall a, alpha a $== gamma a).
Defined.

Global Instance is2graph_fun11 {A B : Type} `{Is1Cat A, Is1Cat B}
  : Is2Graph (Fun11 A B)
  := is2graph_induced fun01_fun11.
  
(** In fact, in this case it is automatically also a 0-coherent 2-category and a 1-coherent 1-category, with a totally incoherent notion of 2-cell between 1-coherent natural transformations. *)

Global Instance is1cat_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : Is1Cat (Fun01 A B).
Proof.
  srapply Build_Is1Cat.
  - intros [F ?] [G ?]; srapply Build_Is01Cat.
    + intros [alpha ?] a; cbn.
      reflexivity.
    + intros [alpha ?] [gamma ?] [phi ?] nu mu a.
      exact (mu a $@ nu a).
  - intros [F ?] [G ?]; srapply Build_Is0Gpd.
    intros [alpha ?] [gamma ?] mu a.
    exact ((mu a)^$).
  - intros [F ?] [G ?] [K ?] [alpha ?].
    srapply Build_Is0Functor.
    intros [phi ?] [mu ?] f a.
    exact (alpha a $@L f a).
  - intros [F ?] [G ?] [K ?] [alpha ?].
    srapply Build_Is0Functor.
    intros [phi ?] [mu ?] f a.
    exact (f a $@R alpha a).
  - intros [F ?] [G ?] [K ?] [L ?] [alpha ?] [gamma ?] [phi ?] a; cbn.
    srapply cat_assoc.
  - intros [F ?] [G ?] [K ?] [L ?] [alpha ?] [gamma ?] [phi ?] a; cbn.
    srapply cat_assoc_opp.
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    srapply cat_idl.
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    srapply cat_idr.
Defined.

Global Instance is1cat_fun11 {A B :Type} `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (Fun11 A B)
  := is1cat_induced fun01_fun11.

  (** * Composition of functors *)
  
  Definition fun01_compose {A B C} `{IsGraph A, IsGraph B, IsGraph C}
  : Fun01 B C -> Fun01 A B -> Fun01 A C
  := fun G F => Build_Fun01 _ _ (G o F).
  
  Definition fun01_postcomp {A B C}
  `{IsGraph A, Is1Cat B, Is1Cat C} (F : Fun11 B C)
  : Fun01 A B -> Fun01 A C
  := fun01_compose (A:=A) F.
  
(* Instance Is01CatFunctorCat (A B : Category): Is01Cat (Hom A B) := {|
  Id (F : A $-> B) := nattrans_id F;
  cat_comp (F G K : A $->B) sigma tau := nattrans_comp sigma tau
|}. *)

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

  (** Warning: [F] needs to be a 1-functor for this to be a 0-functor. *)
  Global Instance is0functor_fun01_postcomp {A B C}
  `{IsGraph A, Is1Cat B, Is1Cat C} (F : Fun11 B C)
  : Is0Functor (fun01_postcomp (A:=A) F).
  Proof.
  apply Build_Is0Functor.
  intros a b f.
  rapply nattrans_postwhisker.
  exact f.
  Defined.
  
  Global Instance is1functor_fun01_postcomp {A B C}
  `{IsGraph A, Is1Cat B, Is1Cat C} (F : Fun11 B C)
  : Is1Functor (fun01_postcomp (A:=A) F).
  Proof.
  apply Build_Is1Functor.
  - intros a b f g p x.
    rapply fmap2.
    rapply p.
  - intros f x.
    rapply fmap_id.
  - intros a b c f g x.
    rapply fmap_comp.
  Defined.
  
  Definition fun11_fun01_postcomp {A B C}
  `{IsGraph A, Is1Cat B, Is1Cat C} (F : Fun11 B C)
  : Fun11 (Fun01 A B) (Fun01 A C)
  := Build_Fun11 _ _ (fun01_postcomp F).
  
  Definition fun11_compose {A B C} `{Is1Cat A, Is1Cat B, Is1Cat C}
  : Fun11 B C -> Fun11 A B -> Fun11 A C.
  Proof.
  intros F G.
  nrapply Build_Fun11.
  rapply (is1functor_compose G F).
  Defined.

Instance Is01CatCat : Is01Cat Category := {|
    Id (A : Category) := fun11_id (A:=A) ;
    cat_comp A B C := fun11_compose (A:=A) (B:=B) (C:=C)
  |}.


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
  nrapply Build_NatTrans.
  rapply (is1natural_natequiv alpha).
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
  snrapply Build_NatEquiv.
  - intro a.
    refine (Build_CatEquiv (alpha a)).
  - snrapply Build_Is1Natural'.
    + intros a a' f.
      refine ((cate_buildequiv_fun _ $@R _) $@ _ $@ (_ $@L cate_buildequiv_fun _)^$).
      apply (isnat alpha).
    + intros a a' f.
      refine ((_ $@L cate_buildequiv_fun _) $@ _ $@ (cate_buildequiv_fun _ $@R _)^$).
      apply (isnat_tr alpha).
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

Instance Is0Functor_precomp_Cat {A B C : Category} (F : A $-> B) : 
  Is0Functor (cat_precomp C F).
Proof.
  apply Build_Is0Functor.
  intros G H sigma.
  apply (nattrans_prewhisker sigma F).
Defined.

Instance Is0Functor_postcomp_Cat {A B C : Category} (K : B $-> C) : 
  Is0Functor (cat_postcomp A K).
Proof.
  apply Build_Is0Functor.
  intros F G tau.
  apply (nattrans_postwhisker K tau).
Defined.

Lemma natequiv_op {A B : Type} `{Is01Cat A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv (G : A^op -> B^op) F.
Proof.
  intros [a n].
  snrapply Build_NatEquiv.
  1: exact a.
  by rapply is1natural_op.
Defined.

(** We can form the inverse natural equivalence by inverting each map in the family. The naturality proof follows from standard lemmas about inverses. *)
Definition natequiv_inverse {A B : Type} `{IsGraph A} `{HasEquivs B}
  {F G : A -> B} `{!Is0Functor F, !Is0Functor G}
  : NatEquiv F G -> NatEquiv G F.
Proof.
  intros [alpha I].
  snrapply Build_NatEquiv.
  1: exact (fun a => (alpha a)^-1$).
  snrapply Build_Is1Natural'.
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
  snrapply Build_NatEquiv.
  1: intro; reflexivity.
  snrapply Build_Is1Natural.
  intros X Y f.
  refine (cat_prewhisker (id_cate_fun _) _ $@ cat_idl _ $@ _^$).
  refine (cat_postwhisker _ (id_cate_fun _) $@ cat_idr _).
Defined.

Global Instance hasequivs_fun01 (A B : Type) `{Is01Cat A} `{HasEquivs B}
  : HasEquivs (Fun01 A B).
Proof.
  srapply Build_HasEquivs.
  1: intros F G; exact (NatEquiv F G).
  all: intros F G alpha; cbn in *.
  - exact (forall a, CatIsEquiv (alpha a)).
  - exact alpha.
  - intros a; exact _.
  - apply Build_NatEquiv'.
  - cbn; intros; apply cate_buildequiv_fun.
  - exact (natequiv_inverse alpha).
  - intros; apply cate_issect.
  - intros; apply cate_isretr.
  - intros [gamma ?] r s a; cbn in *.
    refine (catie_adjointify (alpha a) (gamma a) (r a) (s a)).
Defined.

Global Instance hasequivs_fun11 {A B : Type} `{Is1Cat A} `{HasEquivs B}
  : HasEquivs (Fun11 A B)
  := hasequivs_induced fun01_fun11.

(** It also inherits a notion of equivalence, namely a natural transformation that is a pointwise equivalence.  Note that this is not a "fully coherent" notion of equivalence, since the functors and transformations are not themselves fully coherent. *)

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

Instance Is3GraphCat : Is3Graph Category := fun A B F G => 
   {| Hom (sigma tau : NatTrans F G) := Transformation sigma tau |}.
(* 
Definition WildModification {A B : Type} (F G: A -> B)
  `{Is1Functor A B F} `{!Is0Functor G,!Is1Functor G} 
  (sigma tau : F $=> G) := Transformation sigma tau. *)

(* TODO: *)
(* Morphisms of natural transformations - Modifications *)
(* Since [Transformation] is dependent, we can define a modification to be a transformation together with a cylinder condition. This doesn't seem to be too useful as of yet however. We would also need better ways to write down cylinders. *)
