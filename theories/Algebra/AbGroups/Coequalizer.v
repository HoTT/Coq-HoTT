From HoTT Require Import Basics Types.
Require Import WildCat.Core WildCat.Square WildCat.Equiv Truncations.Core.
Require Import Groups.Group Groups.QuotientGroup AbelianGroup AbHom.

Local Open Scope mc_add_scope.

(** * Coequalizers of maps [f g : A $-> B] between abelian groups *)

(** Using the cokernel and addition and negation for the homs of abelian groups, we can define the coequalizer of two group homomorphisms as the cokernel of their difference. *)
Definition ab_coeq {A B : AbGroup} (f g : A $-> B)
  := ab_cokernel ((-f) + g).

Definition ab_coeq_in {A B : AbGroup} {f g : A $-> B} : B $-> ab_coeq f g.
Proof.
  exact grp_quotient_map.
Defined.

Definition ab_coeq_glue {A B : AbGroup} {f g : A $-> B}
  : ab_coeq_in (f:=f) (g:=g) $o f $== ab_coeq_in $o g.
Proof.
  intros x.
  napply qglue.
  apply tr.
  by exists x.
Defined.

Definition ab_coeq_rec {A B : AbGroup} {f g : A $-> B}
  {C : AbGroup} (i : B $-> C) (p : i $o f $== i $o g)
  : ab_coeq f g $-> C.
Proof.
  snapply (grp_quotient_rec _ _ i).
  cbn.
  intros b H.
  strip_truncations.
  destruct H as [a q].
  destruct q; simpl.
  lhs napply grp_homo_op.
  lhs napply (ap (+ _)).
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

Definition functor_ab_coeq {A B : AbGroup} {f g : A $-> B} {A' B' : AbGroup} {f' g' : A' $-> B'}
  (a : A $-> A') (b : B $-> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  : ab_coeq f g $-> ab_coeq f' g'.
Proof.
  snapply ab_coeq_rec.
  1: exact (ab_coeq_in $o b).
  refine (cat_assoc _ _ _ $@ _ $@ cat_assoc_opp _ _ _).
  refine ((_ $@L p^$) $@ _ $@ (_ $@L q)).
  refine (cat_assoc_opp _ _ _ $@ (_ $@R a) $@ cat_assoc _ _ _).
  exact ab_coeq_glue.
Defined.

Definition functor2_ab_coeq {A B : AbGroup} {f g : A $-> B} {A' B' : AbGroup} {f' g' : A' $-> B'}
  {a a' : A $-> A'} {b b' : B $-> B'}
  (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  (p' : f' $o a' $== b' $o f) (q' : g' $o a' $== b' $o g)
  (s : b $== b')
  : functor_ab_coeq a b p q $== functor_ab_coeq a' b' p' q'.
Proof.
  snapply ab_coeq_ind_homotopy.
  intros x.
  exact (ap ab_coeq_in (s x)).
Defined.

Definition functor_ab_coeq_compose {A B : AbGroup} {f g : A $-> B}
  {A' B' : AbGroup} {f' g' : A' $-> B'}
  (a : A $-> A') (b : B $-> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  {A'' B'' : AbGroup} {f'' g'' : A'' $-> B''}
  (a' : A' $-> A'') (b' : B' $-> B'')
  (p' : f'' $o a' $== b' $o f') (q' : g'' $o a' $== b' $o g')
  : functor_ab_coeq a' b' p' q' $o functor_ab_coeq a b p q
  $== functor_ab_coeq (a' $o a) (b' $o b) (hconcat p p') (hconcat q q').
Proof.
  snapply ab_coeq_ind_homotopy.
  simpl; reflexivity.
Defined.

Definition functor_ab_coeq_id {A B : AbGroup} (f g : A $-> B)
  : functor_ab_coeq (Id _) (Id _) (hrefl f) (hrefl g) $== Id _.
Proof.
  snapply ab_coeq_ind_homotopy.
  reflexivity.
Defined.

Definition grp_iso_ab_coeq {A B : AbGroup} {f g : A $-> B}
  {A' B' : AbGroup} {f' g' : A' $-> B'}
  (a : A $<~> A') (b : B $<~> B') (p : f' $o a $== b $o f) (q : g' $o a $== b $o g)
  : ab_coeq f g $<~> ab_coeq f' g'.
Proof.
  snapply cate_adjointify.
  - exact (functor_ab_coeq a b p q).
  - exact (functor_ab_coeq a^-1$ b^-1$ (hinverse a _ p) (hinverse a _ q)).
  - nrefine (functor_ab_coeq_compose _ _ _ _ _ _ _ _
      $@ functor2_ab_coeq _ _ _ _ _ $@ functor_ab_coeq_id _ _).
    exact (cate_isretr b).
  - nrefine (functor_ab_coeq_compose _ _ _ _ _ _ _ _
      $@ functor2_ab_coeq _ _ _ _ _ $@ functor_ab_coeq_id _ _).
    exact (cate_issect b).
Defined.
