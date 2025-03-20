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

Instance Is0Functor_bicat_postcomp `{A: Type} `{IsTruncatedBicat A} (a b c : A) (g : b $->c):
  Is0Functor (cat_postcomp a g).
Proof.
  unfold cat_postcomp.
  exact _.
Defined.

Instance Is0Functor_bicat_precomp `{A: Type} `{IsTruncatedBicat A} (a b c : A) (f : a $->b):
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

(*
  The elaborator has trouble checking this definition, so we tell it to
  resolve typeclasses in the order of their dependencies: first solving
  IsGraph, then solving Is01Cat and Is2Cat, and so on.
  The default typeclass search behavior is apparently
  more complex than that.
*)
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

Unset Typeclasses Dependency Order.

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
  : k $@L (q * p) $== (k $@L q) * (k $@L p) := fmap_comp _ _ _.

Definition cat_prewhisker_pp {A} `{IsBicategory A} {a b c : A}
  {f g h : b $-> c} (k : a $-> b) (p : f $=> g) (q : g $=> h)
  : (q * p) $@R k $== (q $@R k) * (p $@R k) := fmap_comp _ _ _.

Definition cat_exchange {A : Type} `{IsBicategory A} {a b c : A}
  {f f' f'' : a $-> b} {g g' g'' : b $-> c}
  (p : f $=> f') (q : f' $=> f'') (r : g $=> g') (s : g' $=> g'')
  : (s * r) $@@ (q * p) $== (s $@@ q) * (r $@@ p)
  := fmap11_comp _ _ _ _ _.

  (** * Wild (2,1)-categories *)
Class Is21Cat (A : Type) `{Is01Cat A,!Is2Graph A,!Is3Graph A} :=
{
  isbicat : IsBicategory A;
  is0gpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is1gpd_hom : forall (a b : A), Is1Gpd (a $-> b) ;
}.

Close Scope twocat_scope.
