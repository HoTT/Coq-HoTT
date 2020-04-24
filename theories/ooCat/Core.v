(* -*- mode: coq; mode: visual-line -*-  *)

Require Import Basics.
Require Export ooCat.Cat1.

Generalizable Variables m n p A B C.

(** ** Cores and opposites *)

(** The core of a category is obtained by discarding noninvertible morphisms.  We can do this at any selection of dimensions.  We don't make this an [Instance], of course; the user must decide when and how to use it. *)
CoFixpoint isglob_gencore (bs : Stream Bool) `{HasEquivs m A}
  : IsGlob m A.
Proof.
  unshelve econstructor; intros a b; destruct (head bs).
  1:exact (a $<~> b).
  1:exact (a $-> b).
  all: cbn; rapply (isglob_gencore (tail bs)).
Defined.

(** We could combine cores with opposites by using a [Stream Laxity] instead. *)

CoFixpoint isfunctor0_gencore (bs : Stream Bool)
           `{HasEquivs m A, IsCat1 n B}
           (F : A -> B) `{!IsFunctor0 F, !IsFunctor1 F}
  : @IsFunctor0 m A n B (isglob_gencore bs) (isglob_gencore bs) F.
Proof.
  snrapply Build_IsFunctor0; intros a b; cbn; destruct (head bs).
  1:apply (cate_fmap F).
  1:apply (fmap F).
  all:cbn; srapply isfunctor0_gencore. 
Defined.

CoFixpoint iscat0_gencore (bs : Stream Bool) `{IsCat1 m A}
  : @IsCat0 m A (isglob_gencore bs).
Proof.
  unshelve econstructor; cbn; destruct (head bs).
  1: intros a b c g f; exact (g $oE f).
  1: intros a b c g f; exact (g $o f).
  1: intros a; apply cate_id.
  1: intros a; apply cat_id.
  1-4: cbn; intros a b c g; srapply isfunctor0_gencore.
  1: intros _ a b f; exact (f^-1$).    
  1: intros; apply gpd_inv; assumption.
  all: exact _.
Defined.

