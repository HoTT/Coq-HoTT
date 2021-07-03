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
Class Is01Cat (A : Type) `{IsGraph A} :=
{
  Id  : forall (a : A), a $-> a;
  cat_comp : forall (a b c : A), (b $-> c) -> (a $-> b) -> (a $-> c);
}.

Arguments cat_comp {A _ _ a b c} _ _.
Notation "g $o f" := (cat_comp g f).

Definition cat_postcomp {A} `{Is01Cat A} (a : A) {b c : A} (g : b $-> c)
  : (a $-> b) -> (a $-> c)
  := cat_comp g.

Definition cat_precomp {A} `{Is01Cat A} {a b : A} (c : A) (f : a $-> b)
  : (b $-> c) -> (a $-> c)
  := fun g => g $o f.

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

Arguments fmap {A B isgraph_A isgraph_B} F {is0functor_F a b} f : rename.

Class Is2Graph (A : Type) `{IsGraph A}
  := isgraph_hom : forall (a b : A), IsGraph (a $-> b).
Global Existing Instance isgraph_hom | 20.
Typeclasses Transparent Is2Graph.

(** ** Wild 1-categorical structures *)
Class Is1Cat (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f;
  cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f;
}.

Global Existing Instance is01cat_hom.
Global Existing Instance is0gpd_hom.
Global Existing Instance is0functor_postcomp.
Global Existing Instance is0functor_precomp.
Arguments cat_assoc {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_idl {_ _ _ _ _ _ _} f.
Arguments cat_idr {_ _ _ _ _ _ _} f.

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
Class Is1Cat_Strong (A : Type)`{!IsGraph A, !Is2Graph A, !Is01Cat A} := 
{
  is01cat_hom_strong : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom_strong : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp_strong : forall (a b c : A) (g : b $-> c),
    Is0Functor (cat_postcomp a g) ;
  is0functor_precomp_strong : forall (a b c : A) (f : a $-> b),
    Is0Functor (cat_precomp c f) ;
  cat_assoc_strong : forall (a b c d : A)
    (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f = h $o (g $o f) ;
  cat_idl_strong : forall (a b : A) (f : a $-> b), Id b $o f = f ;
  cat_idr_strong : forall (a b : A) (f : a $-> b), f $o Id a = f ;
}.

Arguments cat_assoc_strong {_ _ _ _ _ _ _ _ _} f g h.
Arguments cat_idl_strong {_ _ _ _ _ _ _} f.
Arguments cat_idr_strong {_ _ _ _ _ _ _} f.

Definition cat_assoc_opp_strong {A : Type} `{Is1Cat_Strong A}
           {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d)
  : h $o (g $o f) = (h $o g) $o f
  := (cat_assoc_strong f g h)^.

Global Instance is1cat_is1cat_strong (A : Type) `{Is1Cat_Strong A}
  : Is1Cat A | 1000.
Proof.
  srapply Build_Is1Cat.
  all: intros a b.
  - apply is01cat_hom_strong.
  - apply is0gpd_hom_strong.
  - apply is0functor_postcomp_strong.
  - apply is0functor_precomp_strong.
  - intros; apply GpdHom_path, cat_assoc_strong.
  - intros; apply GpdHom_path, cat_idl_strong.
  - intros; apply GpdHom_path, cat_idr_strong.
Defined.

(** Initial objects *)
Definition IsInitial {A : Type} `{Is1Cat A} (x : A)
  := forall (y : A), {f : x $-> y & forall g, f $== g}.
Existing Class IsInitial.

Definition mor_initial {A : Type} `{Is1Cat A} (x y : A) {h : IsInitial x}
  : x $-> y
  := (h y).1.

Definition mor_initial_unique {A : Type} `{Is1Cat A} (x y : A) {h : IsInitial x}
  (f : x $-> y)
  : mor_initial x y $== f
  := (h y).2 f.

(** Terminal objects *)
Definition IsTerminal {A : Type} `{Is1Cat A} (y : A)
  := forall (x : A), {f : x $-> y & forall g, f $== g}.
Existing Class IsTerminal.

Definition mor_terminal {A : Type} `{Is1Cat A} (x y : A) {h : IsTerminal y}
  : x $-> y
  := (h x).1.

Definition mor_terminal_unique {A : Type} `{Is1Cat A} (x y : A) {h : IsTerminal y}
  (f : x $-> y)
  : mor_terminal x y $== f
  := (h x).2 f.

(** Generalizing function extensionality, "Morphism extensionality" states that homwise [GpdHom_path] is an equivalence. *)
Class HasMorExt (A : Type) `{Is1Cat A} := {
  isequiv_Htpy_path : forall a b f g, IsEquiv (@GpdHom_path (a $-> b) _ _ _ f g)
}.

Global Existing Instance isequiv_Htpy_path.

Definition path_hom {A} `{HasMorExt A} {a b : A} {f g : a $-> b} (p : f $== g)
  : f = g
  := GpdHom_path^-1 p.

(** A 1-category with morphism extensionality induces a strong 1-category *)
Global Instance is1cat_strong_hasmorext {A : Type} `{HasMorExt A}
  : Is1Cat_Strong A.
Proof.
  rapply Build_Is1Cat_Strong; hnf; intros; apply path_hom.
  + apply cat_assoc.
  + apply cat_idl.
  + apply cat_idr.
Defined.

(** A 1-functor acts on 2-cells (satisfying no axioms) and also preserves composition and identities up to a 2-cell. *)
  (* The [!] tells Coq to use typeclass search to find the [IsGraph] parameters of [Is0Functor] instead of assuming additional copies of them. *)
Class Is1Functor {A B : Type} `{Is1Cat A} `{Is1Cat B}
  (F : A -> B) `{!Is0Functor F} :=
{
  fmap2 : forall a b (f g : a $-> b), (f $== g) -> (fmap F f $== fmap F g) ;
  fmap_id : forall a, fmap F (Id a) $== Id (F a);
  fmap_comp : forall a b c (f : a $-> b) (g : b $-> c),
    fmap F (g $o f) $== fmap F g $o fmap F f;
}.

Arguments fmap2 {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F a b f g} p : rename.
Arguments fmap_id {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F} a : rename.
Arguments fmap_comp {A B
  isgraph_A is2graph_A is01cat_A is1cat_A
  isgraph_B is2graph_B is01cat_B is1cat_B}
  F {is0functor_F is1functor_F a b c} f g : rename.

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
    srapply Build_Is0Functor.
    intros a b f; apply Id.
  Defined.

  Global Instance is1functor_const
   `{Is1Cat A} `{Is1Cat B} (x : B)
    : Is1Functor (fun _ : A => x).
  Proof.
    srapply Build_Is1Functor.
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

(** We give all arguments names in order to refer to them later. This allows us to write things like [is0functor (isgraph_A := _)] without having to make all the variables explicit. *)
Arguments is0functor_compose {A B C} {isgraph_A isgraph_B isgraph_C}
  F {is0functor_F} G {is0functor_G} : rename.

Arguments is1functor_compose {A B C}
  {isgraph_A is2graph_A is01cat_A is1cat_A
   isgraph_B is2graph_B is01cat_B is1cat_B
   isgraph_C is2graph_C is01cat_C is1cat_C}
  F {is0functor_F} {is1functor_F}
  G {is0functor_G} {is1functor_G}
  : rename.

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
  refine ((cat_idr p^$)^$ $@ (p^$ $@L r^$) $@ _).
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
  := (gpd_moveR_hV s^$)^$.

Definition gpd_moveL_Vh {A : Type} `{Is1Gpd A} {x y z : A} {p : y $-> z}
  {q : x $-> y} {r : x $-> z} (s : p $o q $== r) 
  : q $== p^$ $o r 
  := (gpd_moveR_Vh s^$)^$.

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
  refine (cat_assoc _ _ _ $@ (f $@L gpd_h_Vh g f^$) $@ gpd_isretr f).
Defined.

Class Is3Graph (A : Type) `{Is2Graph A}
  := isgraph_hom_hom : forall (a b : A), Is2Graph (a $-> b).
Global Existing Instance isgraph_hom_hom | 30.
Typeclasses Transparent Is3Graph.

(** *** Preservation of initial and terminal objects *)

Class PreservesInitial {A B : Type} (F : A -> B)
  `{Is1Functor A B F} : Type
  := isinitial_preservesinitial
    : forall (x : A), IsInitial x -> IsInitial (F x).
Global Existing Instance isinitial_preservesinitial.

(** The initial morphism is preserved by such a functor. *)
Lemma fmap_initial {A B : Type} (F : A -> B)
  `{PreservesInitial A B F} (x y : A) (h : IsInitial x)
  : fmap F (mor_initial x y) $== mor_initial (F x) (F y).
Proof.
  exact (mor_initial_unique _ _ _)^$.
Defined.

Class PreservesTerminal {A B : Type} (F : A -> B)
  `{Is1Functor A B F} : Type
  := isterminal_preservesterminal
    : forall (x : A), IsTerminal x -> IsTerminal (F x).
Global Existing Instance isterminal_preservesterminal.

(** The terminal morphism is preserved by such a functor. *)
Lemma fmap_terminal {A B : Type} (F : A -> B)
  `{PreservesTerminal A B F} (x y : A) (h : IsTerminal y)
  : fmap F (mor_terminal x y) $== mor_terminal (F x) (F y).
Proof.
  exact (mor_terminal_unique _ _ _)^$.
Defined.

