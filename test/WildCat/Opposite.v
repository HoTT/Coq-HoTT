From HoTT Require Import Basics WildCat.Core WildCat.Opposite.

(** * Opposites are (almost) definitionally involutive. *)

Definition test1 A : A = (A^op)^op :> Type := 1.
Definition test2 A `{x : IsGraph A} : x = @isgraph_op A^op (@isgraph_op A x) := 1.
Definition test3 A `{x : Is01Cat A} : x = @is01cat_op A^op _ (@is01cat_op A _ x) := 1.
Definition test4 A `{x : Is2Graph A} : x = @is2graph_op A^op _ (@is2graph_op A _ x) := 1.

(** [Is1Cat] is not definitionally involutive. *)
Fail Definition test5 A `{x : Is1Cat A} : x = @is1cat_op A^op _ _ _ (@is1cat_op A _ _ _ x) := 1.

(** However, everything in [Is1Cat] except for [cat_assoc] *is* definitionally involutive. We can either omit [cat_assoc], or use the following trick to keep it. *)
Class Is1Cat' (A : Type) `{!IsGraph A, !Is2Graph A, !Is01Cat A} :=
{
  is01cat_hom : forall (a b : A), Is01Cat (a $-> b) ;
  is0gpd_hom : forall (a b : A), Is0Gpd (a $-> b) ;
  is0functor_postcomp : forall (a b c : A) (g : b $-> c), Is0Functor (cat_postcomp a g) ;
  is0functor_precomp : forall (a b c : A) (f : a $-> b), Is0Functor (cat_precomp c f) ;
  cat_assoc : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    (h $o g) $o f $== h $o (g $o f);
  cat_assoc_opp : forall (a b c d : A) (f : a $-> b) (g : b $-> c) (h : c $-> d),
    h $o (g $o f) $== (h $o g) $o f;
  cat_idl : forall (a b : A) (f : a $-> b), Id b $o f $== f;
  cat_idr : forall (a b : A) (f : a $-> b), f $o Id a $== f;
}.

(** This is a modified version of [is1cat_op] that inlines a few arguments. *)
Definition is1cat_op' {A : Type} `{Is1Cat' A} : Is1Cat' A^op.
Proof.
  snrapply Build_Is1Cat'; unfold op in *; cbv in *.
  - intros a b.
    apply is01cat_hom.
  - intros a b.
    apply is0gpd_hom.
  - intros a b c h.
    srapply Build_Is0Functor.
    intros f g p.
    cbn in *.
    exact (fmap (cat_precomp a h) (is0functor_F:=is0functor_precomp _ _ a h) p).
  - intros a b c h.
    srapply Build_Is0Functor.
    intros f g p.
    cbn in *.
    exact (fmap (cat_postcomp c h) (is0functor_F:=is0functor_postcomp _ _ _ h) p).
  - intros a b c d f g h.
    exact (cat_assoc_opp _ _ _ _ h g f).
  - intros a b c d f g h.
    exact (cat_assoc _ _ _ _ h g f).
  - intros a b f; exact (cat_idr _ _ f).
  - intros a b f; exact (cat_idl _ _ f).
Defined.

Definition test6 A `{x : Is1Cat' A} : x = @is1cat_op' A^op _ _ _ (@is1cat_op' A _ _ _ x) := 1.
