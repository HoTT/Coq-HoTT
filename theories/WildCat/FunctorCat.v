(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics Types.Sigma.
Require Import WildCat.Core.
Require Import WildCat.Equiv.
Require Import WildCat.Induced.
Require Import WildCat.NatTrans.

(** * Wild functor categories *)

(** ** Categories of 0-coherent 1-functors *)

Record Fun01 (A B : Type) `{IsGraph A} `{IsGraph B} := {
  fun01_F : A -> B;
  fun01_is0functor : Is0Functor fun01_F;
}.

Coercion fun01_F : Fun01 >-> Funclass.
Global Existing Instance fun01_is0functor.

Arguments Build_Fun01 A B {isgraph_A isgraph_B} F {fun01_is0functor} : rename.

Definition issig_Fun01 (A B : Type) `{IsGraph A} `{IsGraph B}
  : _  <~> Fun01 A B := ltac:(issig).

(* Note that even if [A] and [B] are fully coherent oo-categories, the objects of our "functor category" are not fully coherent.  Thus we cannot in general expect this "functor category" to itself be fully coherent.  However, it is at least a 0-coherent 1-category, as long as [B] is a 1-coherent 1-category. *)

Global Instance isgraph_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : IsGraph (Fun01 A B).
Proof.
  srapply Build_IsGraph.
  intros [F ?] [G ?].
  exact (NatTrans F G).
Defined.

Global Instance is01cat_fun01 (A B : Type) `{IsGraph A} `{Is1Cat B} : Is01Cat (Fun01 A B).
Proof.
  srapply Build_Is01Cat.
  - intros [F ?]; cbn.
    exists (id_transformation F); exact _.
  - intros [F ?] [G ?] [K ?] [gamma ?] [alpha ?]; cbn in *.
    exists (trans_comp gamma alpha); exact _.
Defined.

Global Instance is2graph_fun01 (A B : Type) `{IsGraph A, Is1Cat B}
  : Is2Graph (Fun01 A B).
Proof.
  intros [F ?] [G ?]; apply Build_IsGraph.
  intros [alpha ?] [gamma ?].
  exact (forall a, alpha a $== gamma a).
Defined.

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
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    srapply cat_idl.
  - intros [F ?] [G ?] [alpha ?] a; cbn.
    srapply cat_idr.
Defined.

(** It also inherits a notion of equivalence, namely a natural transformation that is a pointwise equivalence.  Note that this is not a "fully coherent" notion of equivalence, since the functors and transformations are not themselves fully coherent. *)

Global Instance hasequivs_fun01 (A B : Type) `{Is01Cat A} `{HasEquivs B}
  : HasEquivs (Fun01 A B).
Proof.
  srapply Build_HasEquivs.
  1:{ intros [F ?] [G ?]. exact (NatEquiv F G). }
  1:{ intros [F ?] [G ?] [alpha ?]; cbn in *.
      exact (forall a, CatIsEquiv (alpha a)). }
  all:intros [F ?] [G ?] [alpha alnat]; cbn in *.
  - exists (fun a => alpha a); assumption.
  - intros a; exact _.
  - intros ?.
    snrapply Build_NatEquiv.
    + intros a; exact (Build_CatEquiv (alpha a)).
    + cbn. refine (is1natural_homotopic alpha _).
      intros a; apply cate_buildequiv_fun.
  - cbn; intros; apply cate_buildequiv_fun.
  - exists (fun a => (alpha a)^-1$).
    intros a b f.
    refine ((cat_idr _)^$ $@ _).
    refine ((_ $@L (cate_isretr (alpha a))^$) $@ _).
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L (cat_assoc_opp _ _ _)) $@ _).
    refine ((_ $@L ((isnat (fun a => alpha a) f)^$ $@R _)) $@ _).
    refine ((_ $@L (cat_assoc _ _ _)) $@ _).
    refine (cat_assoc_opp _ _ _ $@ _).
    refine ((cate_issect (alpha b) $@R _) $@ _).
    exact (cat_idl _).
  - intros; apply cate_issect.
  - intros; apply cate_isretr.
  - intros [gamma ?] r s a; cbn in *.
    refine (catie_adjointify (alpha a) (gamma a) (r a) (s a)).
Defined.
(* 
(** Funext seems to be needed to get morphism extensionality in the functor category. *)
Global Instance hasmorext_fun01 `{Funext} (A B : Type)
  `{Is01Cat A, HasEquivs B}
  `{!HasMorExt B}
  : HasMorExt (Fun01 A B).
Proof.
  snrapply Build_HasMorExt.
  intros F G i j.
  
  srapply isequiv_adjointify.
  { intros p.
    srapply (equiv_ap' (issig_NatTrans _ _)^-1 _ _)^-1.
    srapply equiv_path_sigma.
    srefine (_;_).
    { funext x.
      rapply path_hom.
      rapply p. }
    simpl.
    
    unfold Transformation.
    funext x y z.
    Require Import Types.Forall.
    rewrite 3 transport_forall.
    
    simpl.
    
    simpl.
    rapply path_hom.
    rewrite transport_forall_co.
    hnf.
    simpl.
    cbn in p.
    set ((path_forall _ _ (fun x : A => path_hom (p x)))) as q.
    clearbody q.
    rewrite <- (inv_V q).
    
    destruct q^.
    cbn.
    cbv.
    destruct ( apD10^-1 (fun x : A => GpdHom_path^-1 (p x))).
    
  
  
  
Admitted.
 *)
(** ** Categories of 1-coherent 1-functors *)

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

Global Instance isgraph_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : IsGraph (Fun11 A B)
  := isgraph_induced fun01_fun11.

Global Instance is01cat_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
  : Is01Cat (Fun11 A B)
  := is01cat_induced fun01_fun11.

Global Instance is2graph_fun11 {A B : Type} `{Is1Cat A, Is1Cat B}
  : Is2Graph (Fun11 A B)
  := is2graph_induced fun01_fun11.

Global Instance is1cat_fun11 {A B :Type} `{Is1Cat A} `{Is1Cat B}
  : Is1Cat (Fun11 A B)
  := is1cat_induced fun01_fun11.

Global Instance hasequivs_fun11 {A B : Type} `{Is1Cat A} `{HasEquivs B}
  : HasEquivs (Fun11 A B)
  := hasequivs_induced fun01_fun11.

(** * Identity functors *)

Definition fun01_id {A} `{IsGraph A} : Fun01 A A
  := Build_Fun01 A A idmap.

Definition fun11_id {A} `{Is1Cat A} : Fun11 A A
  := Build_Fun11 _ _ idmap.

(** * Composition of functors *)

Definition fun01_compose {A B C} `{IsGraph A, IsGraph B, IsGraph C}
  : Fun01 B C -> Fun01 A B -> Fun01 A C.
Proof.
  intros F G.
  nrapply Build_Fun01.
  rapply (is0functor_compose G F).
Defined.

Definition fun01_postcomp {A B C}
  `{IsGraph A, Is1Cat B, Is1Cat C} (F : Fun11 B C)
  : Fun01 A B -> Fun01 A C
  := fun01_compose (A:=A) F.

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



