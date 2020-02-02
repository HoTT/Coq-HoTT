(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.

(** * Wild categories, functors, and transformations *)

(** ** Directed graphs *)

Class IsGraph (A : Type) :=
{
  Hom : A -> A -> Type
}.

Notation "a $-> b" := (Hom a b).

(** ** 0-categorical structures *)

(** A wild (0,1)-category has 1-morphisms and operations on them, but no coherence. *)
Class Is01Cat (A : Type) := Build_Is01Cat'
{
  isgraph_1cat : IsGraph A;
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Global Existing Instance isgraph_1cat.
Arguments cat_comp {A _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

Definition cat_postcomp {A} `{Is01Cat A} (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c)
  := cat_comp g.

Definition cat_precomp {A} `{Is01Cat A} {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c)
  := fun g => g $o f.

Definition Build_Is01Cat A
           (Hom' : A -> A -> Type)
           (Id'  : forall (a : A), Hom' a a)
           (cat_comp' : forall (a b c : A), Hom' b c -> Hom' a b -> Hom' a c)
  : Is01Cat A
  := Build_Is01Cat' A (Build_IsGraph A Hom') Id' cat_comp'.

(** A wild 0-groupoid is a wild (0,1)-category whose morphisms can be reversed.  This is also known as a setoid. *)
Class Is0Gpd (A : Type) `{Is01Cat A} :=
  { gpd_rev : forall {a b : A}, (a $-> b) -> (b $-> a) }.

Definition GpdHom {A} `{Is0Gpd A} (a b : A) := a $-> b.
Notation "a $== b" := (GpdHom a b).

Global Instance reflexive_GpdHom {A} `{Is0Gpd A}
  : Reflexive GpdHom
  := fun a => Id a.

Definition gpd_comp {A} `{Is0Gpd A} {a b c : A}
  : (a $== b) -> (b $== c) -> (a $== c)
  := fun p q => q $o p.
Infix "$@" := gpd_comp.

Global Instance transitive_GpdHom {A} `{Is0Gpd A}
  : Transitive GpdHom
  := fun a b c f g => f $@ g.

Notation "p ^$" := (gpd_rev p).

Global Instance symmetric_GpdHom {A} `{Is0Gpd A}
  : Symmetric GpdHom
  := fun a b f => f^$.

Definition GpdHom_path {A} `{Is0Gpd A} {a b : A} (p : a = b)
  : a $== b.
Proof.
  destruct p; apply Id.
Defined.

(** A 0-functor acts on morphisms, but satisfies no axioms. *)
Class Is0Functor {A B : Type} `{IsGraph A} `{IsGraph B} (F : A -> B)
  := { fmap : forall (a b : A) (f : a $-> b), F a $-> F b }.

Arguments fmap {_ _ _ _} F {_ _ _} f.


(** ** Wild 1-categorical structures *)

(** A wild 1-category (a.k.a. (1,1)-category) has its hom-types enhanced to 0-groupoids, its composition operations to 0-functors in each variable separately (providing whiskering operations), and its composition associative and unital up to these 2-cells. *)
Class Is1Cat (A : Type) `{Is01Cat A} :=
{
  is01cat_hom : forall (a b : A), Is01Cat (a $-> b) ;
  isgpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall a b c d (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_idl : forall a b (f : a $-> b), Id b $o f $== f;
  cat_idr : forall a b (f : a $-> b), f $o Id a $== f;
}.
Global Existing Instance is01cat_hom.
Global Existing Instance isgpd_hom.
Global Existing Instance is0functor_postcomp.
Global Existing Instance is0functor_precomp.
Arguments cat_assoc {_ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _} f.

Definition cat_assoc_opp {A : Type} `{Is1Cat A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) $== (h $o g) $o f
  := (cat_assoc f g h)^$.

(*
Definition Comp2 {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} {h k : b $-> c}
           (q : h $-> k) (p : f $-> g)
  : (h $o f $-> k $o g)
  := ??

Infix "$o@" := Comp2.
*)

Definition cat_postwhisker {A} `{Is1Cat A} {a b c : A}
           {f g : a $-> b} (h : b $-> c) (p : f $== g)
  : h $o f $== h $o g
  := fmap (cat_postcomp a h) p.
Notation "h $@L p" := (cat_postwhisker h p).

Definition cat_prewhisker {A} `{Is1Cat A} {a b c : A}
           {f g : b $-> c} (p : f $== g) (h : a $-> b)
  : f $o h $== g $o h
  := fmap (cat_precomp c h) p.
Notation "p $@R h" := (cat_prewhisker p h).

(** Often, the coherences are actually equalities rather than homotopies. *)
Class Is1Cat_Strong (A : Type) `{Is01Cat A} := 
{
  is01cat_hom_strong : forall (a b : A), Is01Cat (a $-> b) ;
  isgpd_hom_strong : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp_strong : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp_strong : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f);
  cat_idl_strong : forall (a b : A) (f : a $-> b), Id b $o f = f;
  cat_idr_strong : forall (a b : A) (f : a $-> b), f $o Id a = f;
}.

Arguments cat_assoc_strong {_ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _} f.

Definition cat_assoc_opp_strong {A : Type} `{Is1Cat_Strong A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) = (h $o g) $o f
  := (cat_assoc_strong f g h)^.

Global Instance is1cat_is1cat_strong (A : Type) `{Is1Cat_Strong A}
  : Is1Cat A.
Proof.
  srefine (Build_Is1Cat A _ _ _ _ _ _ _ _).
  all:intros a b.
  - apply is01cat_hom_strong.
  - apply isgpd_hom_strong.
  - apply is0functor_postcomp_strong.
  - apply is0functor_precomp_strong.
  - intros; apply GpdHom_path, cat_assoc_strong.
  - intros; apply GpdHom_path, cat_idl_strong.
  - intros; apply GpdHom_path, cat_idr_strong.
Defined.

(** Initial objects *)
Definition IsInitial {A : Type} `{Is1Cat A} (x : A)
  := forall (y : A), {f : x $-> y & forall g, g $== f}.
Existing Class IsInitial.

(** Terminal objects *)
Definition IsTerminal {A : Type} `{Is1Cat A} (y : A)
  := forall (x : A), {f : x $-> y & forall g, g $== f}.
Existing Class IsTerminal.

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is1Cat A} :=
  { isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ f g) }.
Global Existing Instance isequiv_Htpy_path.

Definition path_hom {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g) : f = g
  := GpdHom_path^-1 p.

(** A 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)
Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (* The [!] tells Coq to use typeclass search to find the [IsGraph] parameters of [Is0Functor] instead of assuming additional copies of them. *)
      (F : A -> B) `{!Is0Functor F} :=
{
  fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) ;
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap2 {A B _ _ _ _} F {_ _ _ _ _ _} p.
Arguments fmap_id {A B _ _ _ _} F {_ _} a.
Arguments fmap_comp {A B _ _ _ _} F {_ _ _ _ _} f g.




(** Identity functor *)

Section IdentityFunctor.

  Context {A : Type} `{Is1Cat A}.

  Global Instance is0functor_idmap : Is0Functor idmap.
  Proof.
    by apply Build_Is0Functor.
  Defined.

  Global Instance is1functor_idmap : Is1Functor idmap.
  Proof.
    by apply Build_Is1Functor.
  Defined.

End IdentityFunctor.

(** Constant functor *)

Section ConstantFunctor.

  Context {A B : Type}.

  Global Instance is01functor_const
    `{IsGraph A} `{Is01Cat B} (x : B)
    : Is0Functor (fun _ : A => x).
  Proof.
    serapply Build_Is0Functor.
    intros a b f; apply Id.
  Defined.

  Global Instance is1functor_const
         `{Is1Cat A} `{Is1Cat B} (x : B)
    : Is1Functor (fun _ : A => x).
  Proof.
    serapply Build_Is1Functor.
    - intros a b f g p; apply Id.
    - intro; apply Id.
    - intros a b c f g. cbn.
      symmetry.
      apply cat_idl.
  Defined.

End ConstantFunctor.

(** Composite functors *)

Section CompositeFunctor.

  Context {A B C : Type} `{Is1Cat A} `{Is1Cat B} `{Is1Cat C}
          (F : A -> B) `{!Is0Functor F, !Is1Functor F}
          (G : B -> C) `{!Is0Functor G, !Is1Functor G}.

  Global Instance is0functor_compose : Is0Functor (G o F).
  Proof.
    srapply Build_Is0Functor.
    intros a b f; exact (fmap G (fmap F f)).
  Defined.

  Global Instance is1functor_compose : Is1Functor (G o F).
  Proof.
    srapply Build_Is1Functor.
    - intros a b f g p; exact (fmap2 G (fmap2 F p)).
    - intros a; exact (fmap2 G (fmap_id F a) $@ fmap_id G (F a)).
    - intros a b c f g.
      refine (fmap2 G (fmap_comp F f g) $@ _).
      exact (fmap_comp G (fmap F f) (fmap F g)).
  Defined.

End CompositeFunctor.

(** ** Wild 1-groupoids *)

Class Is1Gpd (A : Type) `{Is1Cat A, !Is0Gpd A} :=
{ 
  gpd_issect : forall {a b : A} (f : a $-> b), f^$ $o f $== Id a ;
  gpd_isretr : forall {a b : A} (f : a $-> b), f $o f^$ $== Id b ;
}.

(** Some more convenient equalities for morphisms in a 1-groupoid. The naming scheme is similar to [PathGroupoids.v].*)

Definition gpd_V_hh {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b) 
  : f^$ $o (f $o g) $== g :=
  (cat_assoc _ _ _)^$ $@ (gpd_issect f $@R g) $@ cat_idl g.

Definition gpd_h_Vh {A} `{Is1Gpd A} {a b c : A} (f : c $-> b) (g : a $-> b) 
  : f $o (f^$ $o g) $== g :=
  (cat_assoc _ _ _)^$ $@ (gpd_isretr f $@R g) $@ cat_idl g.

Definition gpd_hh_V {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b) 
  : (f $o g) $o g^$ $== f :=
  cat_assoc _ _ _ $@ (f $@L gpd_isretr g) $@ cat_idr f.

Definition gpd_hV_h {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : b $-> a) 
  : (f $o g^$) $o g $== f :=
  cat_assoc _ _ _ $@ (f $@L gpd_issect g) $@ cat_idr f.

Definition gpd_moveL_1M {A : Type} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : p $o q^$ $== Id _) : p $== q.
Proof.
  refine ((cat_idr p)^$ $@ (p $@L (gpd_issect q)^$) $@ (cat_assoc _ _ _)^$ $@ _).
  refine ((r $@R q) $@ cat_idl q).
Defined.

Definition gpd_moveL_V1 {A : Type} `{Is1Gpd A} {x y : A} {p : x $-> y}
  {q : y $-> x} (r : p $o q $== Id _) : p^$ $== q.
Proof.
  refine ((cat_idr (p^$))^$ $@ ((p^$) $@L (r^$)) $@ _).
  apply gpd_V_hh.
Defined.

Definition gpd_moveR_hV {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : r $== p $o q) 
  : r $o q^$ $== p 
  := (s $@R q^$) $@ gpd_hh_V _ _.

Definition gpd_moveR_Vh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : r $== p $o q) 
  : p^$ $o r $== q 
  := (p^$ $@L s) $@ gpd_V_hh _ _.

Definition gpd_moveL_hV {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p $o q $== r) 
  : p $== r $o q^$ 
  := (gpd_moveR_hV (s^$))^$.

Definition gpd_moveL_Vh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p $o q $== r) 
  : q $== p^$ $o r 
  := (gpd_moveR_Vh (s^$))^$.

Definition gpd_rev2 {A : Type} `{Is1Gpd A} {x y : A} {p q : x $-> y}
  (r : p $== q) : p^$ $== q^$.
Proof.
  apply gpd_moveL_V1. apply gpd_moveR_hV.
  exact (r $@ (cat_idl q)^$).
Defined.

Definition gpd_rev_pp {A} `{Is1Gpd A} {a b c : A} (f : b $-> c) (g : a $-> b) 
  : (f $o g)^$ $== g^$ $o f^$.
Proof.
  apply gpd_moveL_V1.
  refine (cat_assoc _ _ _ $@ (f $@L gpd_h_Vh g (f^$)) $@ gpd_isretr f).
Defined.
