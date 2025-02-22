Require Import Basics.Overture Basics.Tactics.
Require Import Types.Forall.
Require Import WildCat.Core.
Require Import WildCat.Prod.
Require Import WildCat.Bifunctor.
Require Import WildCat.NatTrans.

(** * A truncated bicategory has the same generating 2-cells as a bicategory but no relations between them.
      A truncated bicategory where all 2-cells are invertible is the same as a 1-category. *)
Class IsTruncatedBicat (A: Type) `{Is01Cat A} `{!Is2Graph A} := {
  is01cat_bicat_hom :: forall (a b : A), Is01Cat (a $-> b);
  is0bifunctor_bicat_comp :: forall (a b c : A),
    Is0Bifunctor (cat_comp (a:=a) (b:=b) (c:=c));
  bicat_assoc : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $-> h $o (g $o f);
  bicat_assoc_opp : forall {a b c d : A} (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $-> (h $o g) $o f;
  bicat_idl : forall {a b : A} (f : a $-> b), Id b $o f $-> f;
  bicat_idl_opp : forall {a b : A} (f : a $-> b), f $-> Id b $o f ;
  bicat_idr : forall {a b : A} (f : a $-> b), f $o Id a $-> f;
  bicat_idr_opp : forall {a b : A} (f : a $-> b), f $-> f $o Id a;
}.

Global Instance Is0Functor_bicat_postcomp `{A: Type} `{IsTruncatedBicat A} (a b c : A) (g : b $->c): 
  Is0Functor (cat_postcomp a g).
Proof.
  unfold cat_postcomp.
  exact _.
Defined.

Global Instance Is0Functor_bicat_precomp `{A: Type} `{IsTruncatedBicat A} (a b c : A) (f : a $->b):
  Is0Functor (cat_precomp c f).
Proof.
  unfold cat_precomp.
  exact _.
Defined.

Declare Scope twocat_scope.
Notation "A $=> B" := (Hom (A:= Hom _ _) A B) : twocat_scope.
(* Vertical composition of 2-cells*)
Notation "g * f" := (cat_comp (A:=Hom _ _) g f) : twocat_scope.

Notation "h $@L p" := (fmap (cat_postcomp _ h) p) : twocat_scope.
Notation "p $@R h" := (fmap (cat_precomp _ h) p) : twocat_scope.
Notation "beta $@@ alpha" := (fmap11 (cat_comp) beta alpha) : twocat_scope.

Open Scope twocat_scope.

Set Typeclasses Dependency Order.

Class IsBicategory (A : Type) `{Is01Cat A} `{!Is2Graph A} `{!Is3Graph A} := {
  is_truncated_bicat:: IsTruncatedBicat A;
  is1cat_2cells:: forall (a b : A), Is1Cat (Hom a b);
  is1bifunctor_bicat_comp :: forall (a b c : A), Is1Bifunctor (cat_comp (a:=a) (b:=b) (c:=c));
  is1functor_bicat_postcomp :: forall (a b c : A) (g : b $-> c), Is1Functor (cat_postcomp a g) := _;
  is1functor_bicat_precomp :: forall (a b c : A) (f : a $-> b), Is1Functor (cat_precomp c f) := _;
  bicat_assoc_inv: forall {a b c d} (f : a $->b) (g : b $-> c) (h : c $->d),
    AreInverse (bicat_assoc f g h) (bicat_assoc_opp f g h);
  bicat_idl_inv : forall {a b} (f : a $-> b), AreInverse (bicat_idl f) (bicat_idl_opp f);
  bicat_idr_inv : forall {a b} (f : a $-> b), AreInverse (bicat_idr f) (bicat_idr_opp f);
  bicat_assoc_nat :: forall {a b c d: A},
    Is1Natural
    (fun '(h, g, f) => h $o g $o f)
    (fun '(h, g, f) => h $o (g $o f))
    (fun '(h, g, f)  => bicat_assoc (a:=a)(b:=b)(c:=c)(d:=d) f g h);
  bicat_idl_nat :: forall {a b : A}, Is1Natural
    (fun f : a $->b => (Id b) $o f)
    (fun f : a $->b => f)
    (fun f : a $->b => bicat_idl f);
  bicat_idr_nat :: forall {a b : A}, Is1Natural
    (fun f : a $->b => f $o (Id a))
    (fun f : a $->b => f)
    (fun f : a $->b => bicat_idr f);
  bicat_pentagon : forall {a b c d e:A} 
    (f : a $-> b) (g : b $->c) (h : c $-> d) (k: d $->e),
    (bicat_assoc (g $o f) h k) $o (bicat_assoc f g (k $o h)) $==
      (fmap (cat_postcomp a k) (bicat_assoc f g h)) $o 
      (bicat_assoc f (h $o g) k) $o
      (fmap (cat_precomp e f) (bicat_assoc g h k));
  bicat_triangle:  forall {a b c:A} (f : a $-> b) (g : b $->c),
    (fmap (cat_postcomp a g) (bicat_idl f)) $o (bicat_assoc f (Id b) g)
    $== (fmap (cat_precomp c f) (bicat_idr g))
}.

Definition bifunctor_coh_comp (A: Type) `{IsBicategory A} :
  forall {a b c : A} {f f' : a $-> b}  {g g' : b $-> c}
    (p : f $=> f') (p' : g $=> g'),
    (g' $@L p) * (p' $@R f) $== (p' $@R f') * (g $@L p).
Proof.
    intros a b c f f' g g' p q.
    apply (bifunctor_coh cat_comp).
Defined.
(** *** Whiskering functoriality *)

Definition cat_postwhisker_pp {A} `{IsBicategory A} {a b c : A}
  {f g h : a $-> b} (k : b $-> c) (p : f $=> g) (q : g $=> h)
  : k $@L (q * p) $== (k $@L q) * (k $@L p).
Proof.
  apply fmap_comp.
  exact _.
Defined.

Definition cat_prewhisker_pp {A} `{IsBicategory A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $=> g) (q : g $=> h)
  : (q * p) $@R k $== (q $@R k) * (p $@R k).
Proof.
  apply fmap_comp.
  exact _.
Defined.

Definition cat_exchange {A : Type} `{IsBicategory A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $=> f') (q : f' $=> f'') (r : g $=> g') (s : g' $=> g'')
  : (s * r) $@@ (q * p) $== (s $@@ q) * (r $@@ p).
Proof.
  apply fmap11_comp.
  exact _.
Defined.

(* (** We have presented a bicategory by stratifying it into
    the lower portion (of 0, 1, and 2-cells) and then the 
    upper portion consisting of 3-cells. We give another
    constructor that takes advantage of existing hom structure
*)
Local Instance Bicat_from_hom_1cat {A :Type}
 ` {H : forall (a b : A), Is1Cat (a $-> b)}: Is1Cat A.
 *)
(* Module Category.
  
End Category. *)

(** * Wild (2,1)-categories *)
Class Is21Cat (A : Type) `{Is01Cat A,!Is2Graph A,!Is3Graph A} :=
{ 
  isbicat : IsBicategory A;
  is0gpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
}.

(* We have to construct several natural transformations which turn out to be
   the identity once the functors are unpacked, so we eliminate the boilerplate *)
#[local]
Ltac construct_nat_Trans := 
  snrapply Build_NatTrans; [
    unfold Transformation; exact (fun _ => Id _)
  | snrapply Build_Is1Natural;
    intros a a' f;
    exact (cat_idl _ $@ (cat_idr _)^$ )
  ].

Definition Cat_assoc {A B C D : Category} 
  (F : A $-> B) (G : B $-> C) (H : C $-> D) :
  NatTrans (H $o G $o F) (H $o (G $o F)) := ltac:(construct_nat_Trans).

Definition Cat_assoc_opp {A B C D : Category} 
  (F : A $-> B) (G : B $-> C) (H : C $-> D) :
  NatTrans (H $o (G $o F)) (H $o G $o F) := ltac:(construct_nat_Trans).

Definition Cat_idl {A B : Category} 
  (F : A $-> B) : NatTrans (F $o Id A) F := ltac:(construct_nat_Trans).

Definition Cat_idl_opp {A B : Category} 
  (F : A $-> B) : NatTrans F (F $o Id A):= ltac:(construct_nat_Trans).

Definition Cat_idr {A B : Category} 
  (F : A $-> B) : NatTrans (Id B $o F) F := ltac:(construct_nat_Trans).

Definition Cat_idr_opp {A B : Category} 
  (F : A $-> B) : NatTrans F (Id B $o F):= ltac:(construct_nat_Trans).

(** The bicategory of categories *)
Instance IsTruncatedBicatCat : IsTruncatedBicat Category := {
  is01cat_bicat_hom := _; 
  is0bifunctor_bicat_comp A B C := (Build_Is0Bifunctor'' _); 
  bicat_assoc _ _ _ _ := Cat_assoc ;
  bicat_assoc_opp _ _ _ _ := Cat_assoc_opp;
  bicat_idl _ _ := Cat_idl; 
  bicat_idl_opp _ _ :=  Cat_idl_opp ;
  bicat_idr _ _ := Cat_idr;
  bicat_idr_opp _ _ := Cat_idr_opp; 
}.

(* Instance is1bifunctor_Cat_comp : forall A B C : Category, 
  Is1Bifunctor (cat_comp (a:=A) (b:=B) (c :=C)).
Proof.
  intros A B C.
  snrapply Build_Is1Bifunctor''.
  - 
Defined. *)

(* Definition isoingeo : IsTruncatedBicat Category := _. *)
(* Print IsBicategory.
#[refine]
Instance IsBicat : IsBicategory Category := {
  is_truncated_bicat := _;
  is1cat_2cells := _;
  is1bifunctor_bicat_comp := _;
  bicat_assoc_inv := _;
  bicat_idl_inv := _;
  bicat_idr_inv := _;
  bicat_assoc_nat := _ ;
  bicat_idl_nat := _ ;
  bicat_idr_nat := _;
  bicat_pentagon := _;
  bicat_triangle := _
}.
Proof.
- exact _.
Defined.

Module Cat.
  
End Cat. *)

Close Scope twocat_scope.
