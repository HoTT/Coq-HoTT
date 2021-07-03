(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
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

Arguments Build_Fun11 {A B _ _ _ _ _ _ _ _} F _ _ : rename.

Definition fun01_fun11 {A B : Type} `{Is1Cat A} `{Is1Cat B}
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
  := Build_Fun01 A A _ _ idmap _.

Definition fun11_id {A} `{Is1Cat A} : Fun11 A A
  := Build_Fun11 idmap _ _.

(** * Composition of functors *)

Definition fun01_compose {A B C} `{IsGraph A, IsGraph B, IsGraph C}
  : Fun01 B C -> Fun01 A B -> Fun01 A C.
Proof.
  intros F G.
  nrapply Build_Fun01.
  rapply (is0functor_compose G F).
Defined.

Definition fun11_compose {A B C} `{Is1Cat A, Is1Cat B, Is1Cat C}
  : Fun11 B C -> Fun11 A B -> Fun11 A C.
Proof.
  intros F G.
  nrapply Build_Fun11.
  rapply (is1functor_compose G F).
Defined.

