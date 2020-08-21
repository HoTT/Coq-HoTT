Require Import Basics Types.
Require Import Algebra.Groups.Group.
Require Import HIT.Coeq.
Require Import Algebra.Groups.FreeProduct.

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.

(** Coequalizers of group homomorphisms *)

Definition GroupCoeq {A B : Group} (f g : GroupHomomorphism A B) : Group.
Proof.
  rapply (AmalgamatedFreeProduct (FreeProduct A A) A B).
  1,2: apply FreeProduct_rec.
  + exact grp_homo_id.
  + exact grp_homo_id.
  + exact f.
  + exact g.
Defined.

Definition equiv_groupcoeq_rec `{Funext} {A B C : Group} (f g : GroupHomomorphism A B)
  : {h : GroupHomomorphism B C & h o f == h o g} <~> GroupHomomorphism (GroupCoeq f g) C.
Proof.
  refine (equiv_amalgamatedfreeproduct_rec _ _ _ _ _ _ oE _).
  refine (equiv_sigma_symm _ oE _).
  apply equiv_functor_sigma_id.
  intros h.
  snrapply equiv_adjointify.
  { intros p.
    exists (grp_homo_compose h f).
    hnf; intro x.
    refine (p _ @ _).
    revert x.
    rapply Trunc_ind.
    srapply Coeq_ind.
    2: intros; apply path_ishprop.
    intros w. hnf.
    induction w.
    1: apply ap, grp_homo_unit.
    simpl.
    destruct a as [a|a].
    1,2: refine (ap _ (grp_homo_op _ _ _) @ _).
    1,2: refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^); f_ap.
    symmetry.
    apply p. }
  { intros [k p] x.
    assert (q1 := p (freeproduct_inl x)).
    assert (q2 := p (freeproduct_inr x)).
    simpl in q1, q2.
    rewrite 2 right_identity in q1, q2.
    refine (q1^ @ q2). }
  { hnf. intros [k p].
    apply path_sigma_hprop.
    simpl.
    apply equiv_path_grouphomomorphism.
    intro y.
    pose (q1 := p (freeproduct_inl y)).
    simpl in q1.
    rewrite 2 right_identity in q1.
    exact q1^. }
  hnf; intros; apply path_ishprop.
Defined.
