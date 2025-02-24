Require Import Basics Types.
Require Import WildCat.Core.
Require Import Truncations.Core.
Require Import Algebra.Groups.Group.
Require Import Colimits.Coeq.
Require Import Algebra.Groups.FreeProduct.
Require Import List.Core.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** Coequalizers of group homomorphisms *)

Definition GroupCoeq {A B : Group} (f g : A $-> B) : Group.
Proof.
  nrapply (AmalgamatedFreeProduct (FreeProduct A A) A B).
  - exact (FreeProduct_rec (Id _) (Id _)).
  - exact (FreeProduct_rec f g).
Defined.

Definition groupcoeq_in {A B : Group} {f g : A $-> B}
  : B $-> GroupCoeq f g
  := amal_inr.

Definition groupcoeq_glue {A B : Group} {f g : A $-> B}
  : groupcoeq_in (f:=f) (g:=g) $o f $== groupcoeq_in $o g.
Proof.
  intros x; simpl.
  rewrite <- (right_identity (f x)).
  rewrite <- (right_identity (g x)).
  rhs_V nrapply (amal_glue (freeproduct_inr x)).
  symmetry.
  nrapply (amal_glue (freeproduct_inl x)).
Defined.

Definition groupcoeq_rec {A B C : Group} (f g : A $-> B)
  (h : B $-> C) (p : h $o f $== h $o g)
  : GroupCoeq f g $-> C.
Proof.
  rapply (AmalgamatedFreeProduct_rec C (h $o f) h).
  snrapply freeproduct_ind_homotopy.
  (** The goals generated are very simple, but we give explicit proofs with wild cat terms to stop Coq from unfolding terms when checking the proof. Note that the category of groups is definitionally associative. *)
  - refine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
    exact ((_ $@L freeproduct_rec_beta_inl _ _) $@ cat_idr _
      $@ (_ $@L freeproduct_rec_beta_inl _ _)^$).
  - refine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
    exact ((_ $@L freeproduct_rec_beta_inr _ _) $@ (cat_idr _ $@ p)
      $@ (_ $@L freeproduct_rec_beta_inr _ _)^$).
Defined.

(** TODO: unify this with [groupcoeq_rec]. It will require doing the analagous thing for [AmalgamatedFreeProduct]. *)
Definition equiv_groupcoeq_rec `{Funext} {A B C : Group} (f g : GroupHomomorphism A B)
  : {h : B $-> C & h o f == h o g} <~> (GroupCoeq f g $-> C).
Proof.
  refine (equiv_amalgamatedfreeproduct_rec _ _ _ _ _ _ oE _).
  refine (equiv_sigma_symm _ oE _).
  apply equiv_functor_sigma_id.
  intros h.
  snapply equiv_adjointify.
  { intros p.
    exists (grp_homo_compose h f).
    hnf; intro x.
    refine (p _ @ _).
    revert x.
    rapply Trunc_ind.
    srapply Coeq_ind_hprop.
    intros w. hnf.
    induction w.
    1: apply ap, grp_homo_unit.
    simpl.
    destruct a as [a|a].
    1,2: refine (ap _ (grp_homo_op _ _ _) @ _).
    1,2: napply grp_homo_op_agree; trivial.
    symmetry.
    apply p. }
  { intros [k p] x.
    assert (q1 := p (freeproduct_inl x)).
    assert (q2 := p (freeproduct_inr x)).
    simpl in q1, q2.
    rewrite 2 right_identity in q1, q2.
    exact (q1^ @ q2). }
  { hnf. intros [k p].
    apply path_sigma_hprop.
    simpl.
    apply equiv_path_grouphomomorphism.
    intro y.
    pose (q1 := p (freeproduct_inl y)).
    simpl in q1.
    rewrite 2 right_identity in q1.
    symmetry.
    exact q1. }
  hnf; intros; apply path_ishprop.
Defined.

Definition groupcoeq_ind_hprop {G H : Group} {f g : G $-> H}
  (P : GroupCoeq f g -> Type) `{forall x, IsHProp (P x)}
  (c : forall h, P (groupcoeq_in h))
  (Hop : forall x y, P x -> P y -> P (x * y))
  : forall x, P x.
Proof.
  srapply amalgamatedfreeproduct_ind_hprop.
  - intros x.
    rewrite <- (right_identity x).
    refine ((amal_glue (freeproduct_inl x))^ #_).
    simpl.
    rewrite (right_identity (f x)).
    exact (c (f x)).
  - exact c.
  - exact Hop.
Defined.

Definition groupcoeq_ind_homotopy {G H K : Group} {f g : G $-> H}
  {h h' : GroupCoeq f g $-> K}
  (r : h $o groupcoeq_in $== h' $o groupcoeq_in)
  : h $== h'.
Proof.
  rapply (groupcoeq_ind_hprop _ r).
  intros x y p q; by nrapply grp_homo_op_agree.
Defined.

Definition functor_groupcoeq
  {G H : Group} {f g : G $-> H} {G' H' : Group} {f' g' : G' $-> H'}
  (h : G $-> G') (k : H $-> H')
  (p : k $o f $== f' $o h) (q : k $o g $== g' $o h)
  : GroupCoeq f g $-> GroupCoeq f' g'.
Proof.
  refine (groupcoeq_rec f g (groupcoeq_in $o k) _).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _). 
  refine ((_ $@L p) $@ _ $@ (_ $@L q^$)).
  refine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ cat_assoc _ _ _). 
  apply groupcoeq_glue.
Defined.
