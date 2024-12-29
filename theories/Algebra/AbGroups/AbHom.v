Require Import Basics Types.
Require Import WildCat HSet Truncations.Core Modalities.ReflectiveSubuniverse.
Require Import Groups.QuotientGroup AbelianGroup Biproduct.

(** * Homomorphisms from a group to an abelian group form an abelian group. *)

(** In this file, we use additive notation for the group operation, even though some of the groups we deal with are not assumed to be abelian. *)
Local Open Scope mc_add_scope.

(** The sum of group homomorphisms [f] and [g] is [fun a => f(a) + g(a)].  While the group *laws* require [Funext], the operations do not, so we make them instances. *)
Global Instance sgop_hom {A : Group} {B : AbGroup} : SgOp (A $-> B).
Proof.
  intros f g.
  exact (grp_homo_compose ab_codiagonal (grp_prod_corec f g)).
Defined.

(** We can negate a group homomorphism [A -> B] by post-composing with [ab_homo_negation : B -> B]. *)
Global Instance inverse_hom {A : Group} {B : AbGroup}
  : Inverse (@Hom Group _ A B) := grp_homo_compose ab_homo_negation.

(** For [A] and [B] groups, with [B] abelian, homomorphisms [A $-> B] form an abelian group. *)
Definition grp_hom `{Funext} (A : Group) (B : AbGroup) : Group.
Proof.
  snrapply (Build_Group' (GroupHomomorphism A B) sgop_hom grp_homo_const inverse_hom).
  1: exact _.
  all: hnf; intros; apply equiv_path_grouphomomorphism; intro; cbn.
  - apply associativity.
  - apply left_identity.
  - apply left_inverse.
Defined.

Definition ab_hom `{Funext} (A : Group) (B : AbGroup) : AbGroup.
Proof.
  snrapply (Build_AbGroup (grp_hom A B)).
  intros f g; cbn.
  apply equiv_path_grouphomomorphism; intro x; cbn.
  apply commutativity.
Defined.

(** ** Coequalizers *)

(** Using the cokernel and addition and negation for the homs of abelian groups, we can define the coequalizer of two group homomorphisms as the cokernel of their difference. *)
Definition ab_coeq {A B : AbGroup} (f g : GroupHomomorphism A B)
  := ab_cokernel ((-f) + g).

Definition ab_coeq_in {A B} {f g : A $-> B} : B $-> ab_coeq f g.
Proof.
  snrapply grp_quotient_map.
Defined.

Definition ab_coeq_glue {A B} {f g : A $-> B}
  : ab_coeq_in (f:=f) (g:=g) $o f $== ab_coeq_in $o g.
Proof.
  intros x.
  nrapply qglue.
  apply tr.
  by exists x.
Defined.

Definition ab_coeq_rec {A B : AbGroup} {f g : A $-> B}
  {C : AbGroup} (i : B $-> C) (p : i $o f $== i $o g) 
  : ab_coeq f g $-> C.
Proof.
  snrapply (grp_quotient_rec _ _ i).
  cbn.
  intros b H.
  strip_truncations.
  destruct H as [a q].
  destruct q; simpl.
  lhs nrapply grp_homo_op.
  lhs nrapply (ap (+ _)).
  1: apply grp_homo_inv.
  apply grp_moveL_M1^-1.
  exact (p a)^.
Defined.

Definition ab_coeq_rec_beta_in {A B : AbGroup} {f g : A $-> B}
  {C : AbGroup} (i : B $-> C) (p : i $o f $== i $o g)
  : ab_coeq_rec i p $o ab_coeq_in $== i
  := fun _ => idpath.

Definition ab_coeq_ind_hprop {A B f g} (P : @ab_coeq A B f g -> Type)
  `{forall x, IsHProp (P x)}
  (i : forall b, P (ab_coeq_in b))
  : forall x, P x.
Proof.
  rapply Quotient_ind_hprop.
  exact i.
Defined.

Definition ab_coeq_ind_homotopy {A B C f g}
  {l r : @ab_coeq A B f g $-> C}
  (p : l $o ab_coeq_in $== r $o ab_coeq_in) 
  : l $== r.
Proof.
  srapply ab_coeq_ind_hprop.
  exact p.
Defined.

Definition functor_ab_coeq {A B} {f g : A $-> B} {A' B'} {f' g' : A' $-> B'}
  (a : A $-> A') (b : B $-> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  : ab_coeq f g $-> ab_coeq f' g'.
Proof.
  snrapply ab_coeq_rec.
  1: exact (ab_coeq_in $o b).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
  refine ((_ $@L p^$) $@ _ $@ (_ $@L q)).
  refine (cat_assoc_opp _ _ _ $@ (_ $@R a) $@ cat_assoc _ _ _).
  nrapply ab_coeq_glue.
Defined.

Definition functor2_ab_coeq {A B} {f g : A $-> B} {A' B'} {f' g' : A' $-> B'}
  {a a' : A $-> A'} {b b' : B $-> B'}
  (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  (p' : f' $o a' $== b' $o f) (q' : g' $o a' $== b' $o g)
  (s : b $== b')
  : functor_ab_coeq a b p q $== functor_ab_coeq a' b' p' q'.
Proof.
  snrapply ab_coeq_ind_homotopy.
  intros x.
  exact (ap ab_coeq_in (s x)).
Defined.

Definition functor_ab_coeq_compose {A B} {f g : A $-> B}
  {A' B'} {f' g' : A' $-> B'} 
  (a : A $-> A') (b : B $-> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  {A'' B''} {f'' g'' : A'' $-> B''}
  (a' : A' $-> A'') (b' : B' $-> B'')
  (p' : f'' $o a' $== b' $o f') (q' : g'' $o a' $== b' $o g')
  : functor_ab_coeq a' b' p' q' $o functor_ab_coeq a b p q
  $== functor_ab_coeq (a' $o a) (b' $o b) (hconcat p p') (hconcat q q').
Proof.
  snrapply ab_coeq_ind_homotopy.
  simpl; reflexivity.
Defined.

Definition functor_ab_coeq_id {A B} (f g : A $-> B)
  : functor_ab_coeq (f:=f) (g:=g) (Id _) (Id _) (hrefl _) (hrefl _) $== Id _.
Proof.
  snrapply ab_coeq_ind_homotopy.
  reflexivity.
Defined.

Definition grp_iso_ab_coeq {A B} {f g : A $-> B} {A' B'} {f' g' : A' $-> B'}
  (a : A $<~> A') (b : B $<~> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  : ab_coeq f g $<~> ab_coeq f' g'.
Proof.
  snrapply cate_adjointify.
  - exact (functor_ab_coeq a b p q).
  - exact (functor_ab_coeq a^-1$ b^-1$ (hinverse _ _ p) (hinverse _ _ q)).
  - nrefine (functor_ab_coeq_compose _ _ _ _ _ _ _ _
      $@ functor2_ab_coeq _ _ _ _ _ $@ functor_ab_coeq_id _ _).
    rapply cate_isretr.
  - nrefine (functor_ab_coeq_compose _ _ _ _ _ _ _ _
      $@ functor2_ab_coeq _ _ _ _ _ $@ functor_ab_coeq_id _ _).
    rapply cate_issect.
Defined.

(** ** The bifunctor [ab_hom] *)

Global Instance is0functor_ab_hom01 `{Funext} {A : Group^op}
  : Is0Functor (ab_hom A).
Proof.
  snrapply (Build_Is0Functor _ AbGroup); intros B B' f.
  snrapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose f g).
  intros phi psi.
  apply equiv_path_grouphomomorphism; intro a; cbn.
  exact (grp_homo_op f _ _).
Defined.

Global Instance is0functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is0Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  snrapply (Build_Is0Functor (Group^op) AbGroup); intros A A' f.
  snrapply Build_GroupHomomorphism.
  1: exact (fun g => grp_homo_compose g f).
  intros phi psi.
  by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is1functor_ab_hom01 `{Funext} {A : Group^op}
  : Is1Functor (ab_hom A).
Proof.
  nrapply Build_Is1Functor.
  - intros B B' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (p (phi a)).
  - intros B phi.
    by apply equiv_path_grouphomomorphism.
  - intros B C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is1functor_ab_hom10 `{Funext} {B : AbGroup@{u}}
  : Is1Functor (flip (ab_hom : Group^op -> AbGroup -> AbGroup) B).
Proof.
  nrapply Build_Is1Functor.
  - intros A A' f g p phi.
    apply equiv_path_grouphomomorphism; intro a; cbn.
    exact (ap phi (p a)).
  - intros A phi.
    by apply equiv_path_grouphomomorphism.
  - intros A C D f g phi.
    by apply equiv_path_grouphomomorphism.
Defined.

Global Instance is0bifunctor_ab_hom `{Funext}
  : Is0Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  rapply Build_Is0Bifunctor''.
Defined.

Global Instance is1bifunctor_ab_hom `{Funext}
  : Is1Bifunctor (ab_hom : Group^op -> AbGroup -> AbGroup).
Proof.
  nrapply Build_Is1Bifunctor''.
  1,2: exact _.
  intros A A' f B B' g phi; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

(** ** Properties of [ab_hom] *)

(** Precomposition with a surjection is an embedding. *)
(* This could be deduced from [isembedding_precompose_surjection_hset], but relating precomposition of homomorphisms with precomposition of the underlying maps is tedious, so we give a direct proof. *)
Global Instance isembedding_precompose_surjection_ab `{Funext} {A B C : AbGroup}
  (f : A $-> B) `{IsSurjection f}
  : IsEmbedding (fmap10 (A:=Group^op) ab_hom f C).
Proof.
  apply isembedding_isinj_hset; intros g0 g1 p.
  apply equiv_path_grouphomomorphism.
  rapply (conn_map_elim (Tr (-1)) f).
  exact (equiv_path_grouphomomorphism^-1 p).
Defined.
