Require Import Basics.Overture.
Require Import WildCat.Core WildCat.Equiv WildCat.PointedCat WildCat.Bifunctor.
Require Import WildCat.Square.
Require Import Algebra.Homological.Biproducts.
Require Import Algebra.AbGroups.AbelianGroup Algebra.Rings.Ring.
Require Import canonical_names.

(** * Semiadditive and Additive Categories *)


(** ** Semiadditive Categories *)

(** As semiadditive category is a a wild category with equivalences and the following data: *)
Class IsSemiAdditive (A : Type) `{HasEquivs A} := {
  (** It is a pointed category. *)
  semiadditive_pointed :: IsPointedCat A;
  (** It has binary biproducts. *)
  semiadditive_hasbiproducts :: HasBinaryBiproducts A;
  (** We have morphism extensionality. *)
  semiadditive_hasmorext :: HasMorExt A;
  (** The homs are set. *)
  semiadditive_ishset_hom :: forall (a b : A), IsHSet (a $-> b);
}.
  
(** The final two conditions in the definition of a semiadditive category ensure that the hom types can become commutative monoids. This is an essential chracteristic of semiadditive categories making it equivalent to alternate defintiions where the category is semiadditive if it is enriched in commutative monoids. The machinary of encriched categories however is a bit heavy so we use this more lightweight definition where the commutative monoid structure appears naturally. *)

Section CMonHom.

  Context {A : Type} `{IsSemiAdditive A} (a b : A).
  
  (** We can show that the hom-types of a semiadditive category are commutative monoids. *)

  (** The zero element is given by the zero morphism. This exists from our pointedness assumption. *)
  Local Instance zero_hom : Zero (a $-> b) := zero_morphism.

  (** TODO: explain a bit more: diagonal duplicates and codiagonal sums. *)
  (** The operation is given by the biproduct structure. *) 
  Local Instance sgop_hom : SgOp (a $-> b) := fun f g =>
    cat_binbiprod_codiag b
    $o fmap11 (fun x y => cat_binbiprod x y) f g
    $o cat_binbiprod_diag a.

  Local Instance left_identity_hom : LeftIdentity sgop_hom zero_hom.
  Proof.
    intros g.
    apply path_hom.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_ $@L cat_assoc _ _ _) $@ _).
    refine ((cat_assoc _ _ _)^$ $@ _).
    snrefine ((_ $@L _) $@ _).
    1: exact cat_binbiprod_inr.
    { apply cat_binbiprod_pr_eta.
      - refine (_ $@ cat_binbiprod_pr1_inr^$).
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr1.
        refine (cat_assoc _ _ _ $@ _).
        apply cat_zero_l.
      - refine (_ $@ cat_binbiprod_pr2_inr^$).
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr2.
        refine (cat_assoc _ _ _ $@ _).
        refine (cat_idl _ $@ _).
        apply cat_binbiprod_corec_beta_pr2. }
    nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
    { refine ((_ $@R _) $@ _).
      1: apply cat_binbiprod_corec_rec.
      apply cat_binbiprod_rec_beta_inr. }
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
    1: apply cat_binbiprod_rec_beta_inr.
    apply cat_idl.
  Defined.

  Local Existing Instance symmetricbraiding_cat_binbiprod.

  (** Using the naturality of swap we can show that the operation is commutative. *)
  Local Instance commutative_hom : Commutative sgop_hom.
  Proof.
    intros f g.
    apply path_hom.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_^$ $@R _) $@ _).
    1: apply cat_binbiprod_swap_codiag.
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: apply cat_binbiprod_swap_diag.
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ cat_assoc _ _ _).
    rapply Monoidal.braid_nat.
  Defined.

  Local Instance right_identity_ab_hom : RightIdentity sgop_hom zero_hom.
  Proof.
    intros f.
    refine (commutativity _ _ @ _).
    apply left_identity_hom.
  Defined.

  Local Instance associative_ab_hom : Associative sgop_hom.
  Proof.
    (** There is a lot to unfold here. But drawing out the diagram we can split this into 5 separate diagrams that all commute. Much of the work here will be applying associativity and functor laws to get this diagram in the correct shape. *)
    intros f g h.
    apply path_hom.
    refine (((_ $@L (_ $@R _)) $@R _) $@ _ $@ ((_ $@L (_ $@L _)^$) $@R _)).
    1,3: refine (_ $@ ((_ $@ (_ $@L _)) $@R _)).
    1-3: rapply fmap01_comp.
    1-3: rapply fmap10_comp.
    Local Notation "a ⊕L g" := (fmap01 (fun x y => cat_binbiprod x y) a g) (at level 99).
    Local Notation "f ⊕R b" := (fmap10 (fun x y => cat_binbiprod x y) f b) (at level 99).
    Local Notation "'Δ' x" := (cat_binbiprod_diag x) (at level 10).
    Local Notation "'∇' x" := (cat_binbiprod_codiag x) (at level 10).
    change (?w $o ?x $== ?y $o ?z) with (Square z w x y).
    apply move_right_top.
    (** The following associativity rewrites are specially chosen so that the diagram can be decomposed easily. *)
    rapply vconcatL.
    1: do 2 refine (cat_assoc _ _ _ $@ _).
    1: refine (((cat_assoc _ _ _)^$ $@R _)).
    rapply vconcatR.
    2: do 2 refine ((cat_assoc _ _ _)^$ $@ (_ $@L (cat_assoc _ _ _)) $@ _).
    2: refine (cat_assoc _ _ _)^$.
    srapply hconcat.
    (** We now have to specify the morphism that we are composing along, i.e. the common edge of the two squares where they meet. This is chosen to be the associativity equivalence for biproducts. *)
    1: nrapply cate_binbiprod_assoc.
    { nrefine ((_ $@R _) $@ _). 
      1: rapply Monoidal.associator_twist'_unfold.
      apply cat_binbiprod_pr_eta.
      - srefine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: exact (fmap01 (fun x y => cat_binbiprod x y) b cat_binbiprod_pr1).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
          1: apply cat_binbiprod_corec_beta_pr1.
          refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
          1: apply cat_binbiprod_corec_beta_pr2.
          refine (_^$ $@ _). 
          1: rapply fmap01_comp.
          refine (fmap02 _ _ _).
          apply cat_binbiprod_corec_beta_pr2. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((((fmap02 _ _ _ $@ fmap01_id _ _ _)^$ $@ fmap01_comp _ _ _ _)^$ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr1.
        nrefine (cat_idl _ $@ _).
        refine (_ $@ (_ $@L (cat_assoc _ _ _)^$)).
        nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ (_^$ $@R _)).
        2: rapply cat_binbiprod_corec_beta_pr1.
        refine ((_ $@L _) $@ (cat_assoc _ _ _)^$).
        nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ (_^$ $@R _)).
        2: rapply cat_binbiprod_corec_beta_pr1.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (_ $@L _^$)).
        2: rapply cat_binbiprod_corec_beta_pr1.
        symmetry.
        apply cat_idr.
      - nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr2.
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr1.
        nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
          apply cat_binbiprod_corec_beta_pr2. }
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr1.
        nrefine ((_ $@L _) $@ _).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
          apply cat_binbiprod_corec_beta_pr2. }
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr2.
        nrefine (cat_idl _ $@ _).
        refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: apply cat_binbiprod_corec_beta_pr2.
        nrefine (cat_assoc _ _ _ $@ _).
        nrefine (cat_idl _ $@ _).
        nrefine (cat_binbiprod_corec_beta_pr2 _ _ $@ _).
        refine (_ $@ (_ $@L (cat_assoc _ _ _)^$)).
        nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ (_^$ $@R _)).
        2: apply cat_binbiprod_corec_beta_pr2.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (cat_idl _)^$).
        refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        2: apply cat_binbiprod_corec_beta_pr2.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (cat_idl _)^$).
        symmetry.
        apply cat_binbiprod_corec_beta_pr2. }
    (** We split the square again, this time by picking yet another associativity map as the common edge. This leaves us with a naturality square for associativity. *)
    srapply hconcat.
    1: nrapply cate_binbiprod_assoc.
    1: nrapply Monoidal.associator_nat_m.
    (** Finally we are left with another polygon which we resolve by brute force. *)
    refine ((cat_assoc _ _ _)^$ $@ _).
    apply cat_binbiprod_in_eta.
    - nrefine (cat_assoc _ _ _ $@ _). 
      nrefine ((_ $@L _) $@ _).
      { nrefine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        apply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_idr _ $@ _).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        apply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_idr _ $@ _).
      refine (_ $@ _).
      1: apply cat_binbiprod_rec_beta_inl.
      symmetry.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: apply cate_binbiprod_assoc_inl.
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        apply cat_binbiprod_rec_beta_inl. }
      simpl.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        apply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
        1: apply cat_binbiprod_rec_beta_inl.
        apply cat_idr. }
      refine (cat_idr _ $@ _).
      apply cat_binbiprod_rec_beta_inl.
    - nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L _) $@ _).
      { nrefine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        apply cat_binbiprod_rec_beta_inr. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      simpl.
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        1: refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        1: apply cat_binbiprod_rec_beta_inr.
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_rec_beta_inr.
        apply cat_idl. }
      simpl.
      refine (_ $@ (cat_assoc _ _ _)^$).
      apply cat_binbiprod_in_eta.
      + refine (cat_assoc _ _ _ $@ _).
        refine ((_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          apply cat_binbiprod_rec_beta_inl. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_rec_beta_inl.
        refine (cat_idr _ $@ _).
        refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
        2: apply cate_binbiprod_assoc_inr_inl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (_ $@L _^$)).
        2: { refine ((cat_assoc _ _ _)^$ $@ _).
          refine ((_ $@R _) $@ _).
          1: refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          1: apply cat_binbiprod_rec_beta_inl.
          simpl.
          refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
          1: apply cat_binbiprod_rec_beta_inr. 
          apply cat_idr. }
        simpl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_^$ $@ (_ $@L _^$)).
        2: { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
          1: apply cat_binbiprod_rec_beta_inl.
          apply cat_idr. }
        apply cat_binbiprod_rec_beta_inl.
      + refine (cat_assoc _ _ _ $@ _).
        refine ((_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          apply cat_binbiprod_rec_beta_inr. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_rec_beta_inr.
        refine (cat_idl _ $@ _).
        refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
        2: apply cate_binbiprod_assoc_inr_inr.
        simpl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_^$ $@ (_ $@L _^$)).
        2: { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
          1: apply cat_binbiprod_rec_beta_inr.
          apply cat_idr. }
        refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          1: apply cat_binbiprod_rec_beta_inr. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: apply cat_binbiprod_rec_beta_inr.
        apply cat_idl.
  Defined.

  Local Instance issemigroup_hom : IsSemiGroup (a $-> b) := {}.
  Local Instance ismonoid_hom : IsMonoid (a $-> b) := {}.

End CMonHom.

(** ** Additive Categories *)

(** *** Definition *)

Class IsAdditive (A : Type) `{HasEquivs A} := {
  additive_semiadditive :: IsSemiAdditive A;
  additive_negate_hom : forall (a b : A), Negate (a $-> b);
  additive_left_inverse_hom : forall (a b : A),
    LeftInverse (sgop_hom a b) (additive_negate_hom a b) (zero_hom a b);
  additive_right_inverse_hom : forall (a b : A),
    RightInverse (sgop_hom a b) (additive_negate_hom a b) (zero_hom a b);
}.

(** *** Abelian Group structure on Hom *)

(** Homs in an aditive category form an abelian group. *)
Definition AbHom {A : Type} `{IsAdditive A} : A -> A -> AbGroup.
Proof.
  intros a b.
  snrapply Build_AbGroup.
  1: snrapply Build_Group.
  5: split.
  - exact (a $-> b).
  - exact (sgop_hom a b).
  - exact (zero_hom a b).
  - exact (additive_negate_hom a b).
  - exact (ismonoid_hom a b).
  - exact (additive_left_inverse_hom a b).
  - exact (additive_right_inverse_hom a b).
  - exact (commutative_hom a b).
Defined.

(** *** Endomorphism ring *)

(** The composition operation provides a multiplicative operation on the abelian group hom. Turning it into a ring of endomorphsims. *)
Definition End {A : Type} `{IsAdditive A} (X : A) : Ring.
Proof.
  snrapply Build_Ring'; repeat split.
  - exact (AbHom X X).
  - exact (fun f g => f $o g).
  - exact (Id _).
  - intros f g h.
    apply path_hom.
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _ $@ cat_assoc _ _ _).
    1: apply cat_binbiprod_codiag_fmap11.
    refine (cat_assoc _ _ _ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
    rapply fmap11_comp.
  - intros f g h.
    apply path_hom.
    refine (cat_assoc _ _ _ $@ _).
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    refine ((_ $@L _) $@ _).
    1: apply cat_binbiprod_diag_fmap11.
    refine ((cat_assoc _ _ _)^$ $@ (_^$ $@R _)).
    rapply fmap11_comp.
  - exact _.
  - intros f g h.
    apply path_hom.
    symmetry.
    apply cat_assoc.
  - intros f.
    apply path_hom.
    apply cat_idl.
  - intros g.
    apply path_hom.
    apply cat_idr.
Defined.

(** TODO: Additive functors *)
