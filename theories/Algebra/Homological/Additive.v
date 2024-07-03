Require Import Basics.Overture.
Require Import WildCat.Core WildCat.Equiv WildCat.PointedCat WildCat.Bifunctor.
Require Import WildCat.Square WildCat.Opposite WildCat.Monoidal NatTrans WildCat.Products WildCat.Coproducts.
Require Import Algebra.Homological.Biproducts.
Require Import Algebra.Groups.Group.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import canonical_names.
Require Import MonoidObject.

(** * Semiadditive and Additive Categories *)


(** ** Semiadditive Categories *)

(** As semiadditive category is a wild category with equivalences and the following data: *)
Class IsSemiAdditive (A : Type) `{HasEquivs A} := {
  (** It is a pointed category. *)
  semiadditive_pointed :: IsPointedCat A;
  (** It has binary biproducts. *)
  semiadditive_hasbiproducts :: HasBinaryBiproducts A;
  (** We have morphism extensionality. *)
  semiadditive_hasmorext :: HasMorExt A;
  (** The homs are sets. *)
  semiadditive_ishset_hom :: forall (a b : A), IsHSet (a $-> b);
}.
  
(** The final two conditions in the definition of a semiadditive category ensure that the hom types can become commutative monoids. This is an essential characteristic of semiadditive categories making it equivalent to alternate definitions where the category is semiadditive if it is enriched in commutative monoids. The machinery of encriched categories however is a bit heavy so we use this more lightweight definition where the commutative monoid structure appears naturally. *)

Local Existing Instance issymmetricmonoidal_cat_binbiprod.

Global Instance iscocommutativecomonoidobject_semiadditive
  {A : Type} `{IsSemiAdditive A} (x : A)
  : IsCocommutativeComonoidObject (fun x y => cat_binprod x y) zero_object x.
Proof.
  snrapply Build_IsCocommutativeComonoidObject.
  { snrapply Build_IsComonoidObject.
    - exact (cat_binbiprod_diag x).
    - exact zero_morphism.
    - refine (_ $@ (cat_binbiprod_fmap10_corec _ _ _)^$).
      nrefine (cat_assoc _ _ _ $@ (_ $@L cat_binbiprod_fmap01_corec _ _ _) $@ _).
      refine ((_ $@L (cat_binbiprod_corec_eta' (Id _) (cat_idr _))) $@ _
        $@ cat_binbiprod_corec_eta' (cat_idr _)^$ (Id _)).
      nrapply Products.cat_binprod_associator_corec.
    - refine (cat_assoc _ _ _ $@ (_ $@L cat_binbiprod_fmap10_corec _ _ _) $@ _).
      nrefine ((cate_buildequiv_fun _ $@R _) $@ _).
      unfold trans_nattrans.
      nrefine (cat_assoc _ _ _ $@ (_ $@L cat_binprod_swap_corec _ _) $@ _).
      nrefine ((cate_buildequiv_fun _ $@R _) $@ _).
      nrapply cat_binbiprod_corec_beta_pr1.
    - refine (cat_assoc _ _ _ $@ (_ $@L cat_binbiprod_fmap01_corec _ _ _) $@ _).
      nrefine ((cate_buildequiv_fun _ $@R _) $@ _).
      nrapply cat_binbiprod_corec_beta_pr1. }
  rapply cat_binprod_swap_corec.
Defined.

Section CMonHom.

  Context {A : Type} `{IsSemiAdditive A} (a b : A).
  
  (** We can show that the hom-types of a semiadditive category are commutative monoids. *)

  Local Instance zero_hom : Zero (a $-> b).
  Proof.
    snrapply MonoidObject.monunit_hom_co.
    1-5: exact _.
    1: exact zero_object.
    1: exact _.
    (* Set Printing All. *)
    (* Check ( cco_co (iscocommutativecomonoidobject_semiadditive a)). *)
    unfold cat_bincoprod.
    snrefine (transport (fun x => @IsComonoidObject _ _ _ _ _ _ _ _ _ x _ _  _ a) _ _).
    3:{
      (* TODO: we need to redefine biproducts so that the coproduct strucutre is emergent from the birpoduct structure rather than being part of the structure. Hopefully this is enough for the following term to be accepted. *)
       pose (i := cco_co (iscocommutativecomonoidobject_semiadditive a)).
      exact i.
    (* Arguments IsComonoidObject : clear implicits.
    Arguments IsCocommutativeComonoidObject : clear implicits.
    pose proof (i := cco_co (iscocommutativecomonoidobject_semiadditive a)).
    unfold cat_bincoprod.
    unfold is1bifunctor_cat_bincoprod.
    Arguments is1bifunctor_op' : clear implicits.
    unfold is1bifunctor_op'.
    unfold is1bifunctor_op.
    
    exact i.
    
    unfold Coproducts.is1bifunctor_cat_bincoprod.
    unfold Coproducts.is1bifunctor_cat_bincoprod.
    
    exact i.
    exact _.
    
    
    

    change (MonUnit (Hom (A:=A^op) b a)).
    snrapply ( (A:=A^op) (zero_object (A:=A^op)) (x := b) (y := a)).
    1-11: exact _.
    (* change (IsMonoidObject (A:=A^op) ?F ?z ?x) with (IsComonoidObject (A:=A) F z x).
      (IsComonoidObject (fun x y => cat_binbiprod x y) _ b). *)
    pose proof (iscocommutativecomonoidobject_semiadditive a). 
    unfold IsCocommutativeComonoidObject in X.
    rapply cmo_mo.
   *)
   Admitted.

  (** TODO: explain a bit more: diagonal duplicates and codiagonal sums. *)
  (** The operation is given by the biproduct structure. *) 
  Global Instance sgop_hom : Plus (a $-> b) := fun f g =>
    cat_binbiprod_codiag b
    $o fmap11 (fun x y => cat_binbiprod x y) f g
    $o cat_binbiprod_diag a.

  Local Instance left_identity_hom : LeftIdentity sgop_hom zero_hom.
  Proof.
    intros g.
    apply path_hom.
    unfold sgop_hom.
    nrefine (cat_assoc _ _ _ $@ (_ $@L (_ $@ _)) $@ _).
    1: nrapply cat_binbiprod_fmap11_corec.
    1: nrapply (cat_binbiprod_corec_eta' (cat_idr _) (cat_idr _) $@ _).
    1: exact (cat_binbiprod_corec_zero_inr g).
    nrefine (cat_assoc_opp _ _ _ $@ (_ $@R _) $@ cat_idl _).
    nrapply cat_binbiprod_rec_beta_inr.
  Defined.
    
  Local Existing Instance symmetricbraiding_cat_binbiprod.

  (** Using the naturality of swap we can show that the operation is commutative. *)
  Local Instance commutative_hom : Commutative sgop_hom.
  Proof.
    intros f g.
    apply path_hom.
    refine (cat_assoc _ _ _ $@ _).
    refine ((_^$ $@R _) $@ _).
    1: nrapply cat_binbiprod_swap_codiag.
    refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
    refine (_ $@ (_ $@L _)).
    2: nrapply cat_binbiprod_swap_diag.
    refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ cat_assoc _ _ _).
    rapply Monoidal.braid_nat.
  Defined.

  Local Instance right_identity_ab_hom : RightIdentity sgop_hom zero_hom.
  Proof.
    intros f.
    refine (commutativity _ _ @ _).
    nrapply left_identity_hom.
  Defined.

  Local Instance associative_ab_hom : Associative sgop_hom.
  Proof.
    (** There is a lot to unfold here. But drawing out the diagram we can split this into 5 separate diagrams that all commute. Much of the work here will be applying associativity and functor laws to get this diagram in the correct shape. *)
    (* intros f g h.
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
    nrapply move_right_top.
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
      nrapply cat_binbiprod_pr_eta.
      - srefine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: exact (fmap01 (fun x y => cat_binbiprod x y) b cat_binbiprod_pr1).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
          1: nrapply cat_binbiprod_corec_beta_pr1.
          refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
          1: nrapply cat_binbiprod_corec_beta_pr2.
          refine (_^$ $@ _). 
          1: rapply fmap01_comp.
          refine (fmap02 _ _ _).
          nrapply cat_binbiprod_corec_beta_pr2. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((((fmap02 _ _ _ $@ fmap01_id _ _ _)^$ $@ fmap01_comp _ _ _ _)^$ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr1.
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
        nrapply cat_idr.
      - nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr2.
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr1.
        nrefine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
          nrapply cat_binbiprod_corec_beta_pr2. }
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr1.
        nrefine ((_ $@L _) $@ _).
        { refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
          nrapply cat_binbiprod_corec_beta_pr2. }
        nrefine ((_ $@L (cat_assoc _ _ _)) $@ _).
        refine ((cat_assoc _ _ _)^$ $@ _).
        nrefine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr2.
        nrefine (cat_idl _ $@ _).
        refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _).
        1: nrapply cat_binbiprod_corec_beta_pr2.
        nrefine (cat_assoc _ _ _ $@ _).
        nrefine (cat_idl _ $@ _).
        nrefine (cat_binbiprod_corec_beta_pr2 _ _ $@ _).
        refine (_ $@ (_ $@L (cat_assoc _ _ _)^$)).
        nrefine (_ $@ cat_assoc _ _ _).
        refine (_ $@ (_^$ $@R _)).
        2: nrapply cat_binbiprod_corec_beta_pr2.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (cat_idl _)^$).
        refine (_ $@ (_^$ $@R _) $@ cat_assoc _ _ _).
        2: nrapply cat_binbiprod_corec_beta_pr2.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (cat_idl _)^$).
        symmetry.
        nrapply cat_binbiprod_corec_beta_pr2. }
    (** We split the square again, this time by picking yet another associativity map as the common edge. This leaves us with a naturality square for associativity. *)
    srapply hconcat.
    1: nrapply cate_binbiprod_assoc.
    1: nrapply Monoidal.associator_nat_m.
    (** Finally we are left with another polygon which we resolve by brute force. *)
    refine ((cat_assoc _ _ _)^$ $@ _).
    nrapply cat_binbiprod_in_eta.
    - nrefine (cat_assoc _ _ _ $@ _). 
      nrefine ((_ $@L _) $@ _).
      { nrefine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        nrapply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_idr _ $@ _).
      refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
      { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        nrapply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine (cat_idr _ $@ _).
      refine (_ $@ _).
      1: nrapply cat_binbiprod_rec_beta_inl.
      symmetry.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      1: nrapply cate_binbiprod_assoc_inl.
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        nrapply cat_binbiprod_rec_beta_inl. }
      simpl.
      refine (cat_assoc _ _ _ $@ _).
      refine ((_ $@L _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        nrapply cat_binbiprod_rec_beta_inl. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _)).
        refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
        1: nrapply cat_binbiprod_rec_beta_inl.
        nrapply cat_idr. }
      refine (cat_idr _ $@ _).
      nrapply cat_binbiprod_rec_beta_inl.
    - nrefine (cat_assoc _ _ _ $@ _).
      nrefine ((_ $@L _) $@ _).
      { nrefine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        nrapply cat_binbiprod_rec_beta_inr. }
      refine ((cat_assoc _ _ _)^$ $@ _).
      simpl.
      refine ((_ $@R _) $@ _).
      { refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        1: refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
        1: nrapply cat_binbiprod_rec_beta_inr.
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_rec_beta_inr.
        nrapply cat_idl. }
      simpl.
      refine (_ $@ (cat_assoc _ _ _)^$).
      nrapply cat_binbiprod_in_eta.
      + refine (cat_assoc _ _ _ $@ _).
        refine ((_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          nrapply cat_binbiprod_rec_beta_inl. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_rec_beta_inl.
        refine (cat_idr _ $@ _).
        refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
        2: nrapply cate_binbiprod_assoc_inr_inl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_ $@ (_ $@L _^$)).
        2: { refine ((cat_assoc _ _ _)^$ $@ _).
          refine ((_ $@R _) $@ _).
          1: refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          1: nrapply cat_binbiprod_rec_beta_inl.
          simpl.
          refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
          1: nrapply cat_binbiprod_rec_beta_inr. 
          nrapply cat_idr. }
        simpl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_^$ $@ (_ $@L _^$)).
        2: { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
          1: nrapply cat_binbiprod_rec_beta_inl.
          nrapply cat_idr. }
        nrapply cat_binbiprod_rec_beta_inl.
      + refine (cat_assoc _ _ _ $@ _).
        refine ((_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          nrapply cat_binbiprod_rec_beta_inr. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_rec_beta_inr.
        refine (cat_idl _ $@ _).
        refine (_ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
        2: nrapply cate_binbiprod_assoc_inr_inr.
        simpl.
        refine (_ $@ (cat_assoc _ _ _)^$).
        refine (_^$ $@ (_ $@L _^$)).
        2: { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ (_ $@ _)).
          1: nrapply cat_binbiprod_rec_beta_inr.
          nrapply cat_idr. }
        refine (cat_assoc _ _ _ $@ (_ $@L _) $@ _).
        { refine ((cat_binbiprod_corec_rec _ _ $@R _) $@ _).
          1: nrapply cat_binbiprod_rec_beta_inr. }
        refine ((cat_assoc _ _ _)^$ $@ _).
        refine ((_ $@R _) $@ _).
        1: nrapply cat_binbiprod_rec_beta_inr.
        nrapply cat_idl. *)
  Admitted.

  Local Instance issemigroup_hom : IsSemiGroup (a $-> b) := {}.
  Local Instance ismonoid_hom : IsMonoid (a $-> b) := {}.

End CMonHom.

(** ** Additive Categories *)

(** *** Definition *)

Class IsAdditive (A : Type) `{HasEquivs A} := {
  additive_semiadditive :: IsSemiAdditive A;
  additive_negate_hom :: forall (a b : A), Negate (a $-> b);
  additive_left_inverse_hom :: forall (a b : A),
    LeftInverse (sgop_hom a b) (additive_negate_hom a b) (zero_hom a b);
  additive_right_inverse_hom :: forall (a b : A),
    RightInverse (sgop_hom a b) (additive_negate_hom a b) (zero_hom a b);
}.

(** *** Abelian Group structure on Hom *)

(** Homs in an additive category form abelian groups. *)
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

(** *** Distributivity of composition over addition *)

Definition addcat_dist_l {A : Type} `{IsAdditive A} {a b c : A}
  (f : b $-> c) (g h : a $-> b)
  : f $o (g + h) $== (f $o g) + (f $o h).
Proof.
  (* refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
  refine ((cat_assoc _ _ _)^$ $@ (_ $@R _) $@ _ $@ cat_assoc _ _ _).
  1: nrapply cat_binbiprod_codiag_fmap11.
  refine (cat_assoc _ _ _ $@ (_ $@L _^$) $@ (cat_assoc _ _ _)^$).
  rapply fmap11_comp. *)
Admitted.

(** Note that this is more general than the distributive law in the endomorphism ring. *)
Global Instance left_heterodistribute_hom {A : Type} `{IsAdditive A} {a b c : A}
  : LeftHeteroDistribute cat_comp (sgop_hom a b) (sgop_hom a c).
Proof.
  intros f g h.
  apply path_hom.
  nrapply addcat_dist_l.
Defined.

Definition addcat_dist_r {A : Type} `{IsAdditive A} {a b c : A}
  (f g : b $-> c) (h : a $-> b)
  : (f + g) $o h $== (f $o h) + (g $o h).
Proof.
  refine (cat_assoc _ _ _ $@ _).
  refine (cat_assoc _ _ _ $@ (_ $@L _) $@ (cat_assoc _ _ _)^$).
  refine ((_ $@L _) $@ _).
  1: nrapply cat_binbiprod_diag_fmap11.
  refine ((cat_assoc _ _ _)^$ $@ (_^$ $@R _)).
  rapply fmap11_comp.
Defined.

Global Instance right_heterodistribute_hom {A : Type} `{IsAdditive A} {a b c : A}
  : RightHeteroDistribute cat_comp (sgop_hom a c) (sgop_hom b c).
Proof.
  intros f g h.
  apply path_hom.
  nrapply addcat_dist_r.
Defined.

Definition addcat_comp_negate_id_l {A : Type} `{IsAdditive A} {a b : A}
  (f : a $-> b)
  : (- Id _) $o f $== -f.
Proof.
  nrapply GpdHom_path.
  change (@paths (Hom a b) ?x ?y) with (@paths (AbHom a b : Type) x y).
  rapply grp_moveL_1V.
  transitivity ((-Id b $o f) + (Id b $o f)).
  - f_ap; symmetry; apply path_hom, cat_idl.
  - lhs_V rapply right_heterodistribute_hom.
    transitivity (zero_morphism (b := b) $o f).
    + f_ap; nrapply (grp_inv_l (Id b : AbHom b b)).
    + apply path_hom.
      nrapply cat_zero_l.
Defined.

Definition addcat_comp_negate_id_r {A : Type} `{IsAdditive A} {a b : A}
  (f : a $-> b)
  : f $o (- Id _) $== -f.
Proof.
  nrapply GpdHom_path.
  change (@paths (Hom a b) ?x ?y) with (@paths (AbHom a b : Type) x y).
  rapply grp_moveL_1V.
  transitivity ((f $o -Id a) + (f $o Id a)).
  - f_ap; symmetry; apply path_hom, cat_idr.
  - lhs_V rapply left_heterodistribute_hom.
    transitivity (f $o zero_morphism (a := a)).
    + f_ap; nrapply (grp_inv_l (Id a : AbHom a a)).
    + apply path_hom.
      nrapply cat_zero_r.
Defined.

Definition addcat_comp_negate_l {A : Type} `{IsAdditive A} {a b c : A}
  (f : b $-> c) (g : a $-> b)
  :  - (f $o g) $== (- f) $o g.
Proof.
  refine ((addcat_comp_negate_id_l _)^$ $@ _).
  refine ((cat_assoc _ _ _)^$ $@ (_ $@R _)).
  nrapply addcat_comp_negate_id_l.
Defined.

Definition addcat_comp_negate_r {A : Type} `{IsAdditive A} {a b c : A}
  (f : b $-> c) (g : a $-> b)
  : - (f $o g) $== f $o (- g).
Proof.
  refine ((addcat_comp_negate_id_r _)^$ $@ _).
  refine (cat_assoc _ _ _ $@ (_ $@L _)).
  nrapply addcat_comp_negate_id_r.
Defined.

(** ** Properties of additive categories *)

(** The opposite of a semiadditive category is semiadditive. *)
Global Instance issemiadditive_op {A : Type} `{IsSemiAdditive A}
  : IsSemiAdditive A^op.
Proof.
  snrapply Build_IsSemiAdditive.
  1-3: exact _.
  intros a b.
  change A in a, b.
  change (IsHSet (b $-> a)).
  exact _.
Defined.

Axiom sorry : Empty.
Ltac sorry := apply Empty_rect; apply sorry.

(** The opposite of an additive category is additive. *)
Global Instance isadditive_op {A : Type} `{H : IsAdditive A}
  : IsAdditive A^op.
Proof.
  snrapply Build_IsAdditive.
  - exact _.
  - intros a b.
    change A in a, b.
    change (Negate (b $-> a)).
    exact _.
  - sorry.
  - sorry.
Defined.

(** TODO: Additive functors *)
