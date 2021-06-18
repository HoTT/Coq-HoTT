Require Import HoTT.Basics HoTT.Types.
Require Import Truncations.
Require Import HIT.Coeq.
Require Export Algebra.Groups.
Require Import Cubical.
Require Import WildCat.

Local Open Scope mc_add_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Record AbGroup := {
  abgroup_group : Group;
  abgroup_commutative : Commutative (@group_sgop abgroup_group);
}.

Coercion abgroup_group : AbGroup >-> Group.
Global Existing Instance abgroup_commutative.

Global Instance isabgroup_abgroup {A : AbGroup} : IsAbGroup A.
Proof.
  split; exact _.
Defined.

Definition issig_abgroup : _ <~> AbGroup := ltac:(issig).

(** ** Paths between abelian groups *)

Definition equiv_path_abgroup `{Univalence} {A B : AbGroup@{u}}
  : GroupIsomorphism A B <~> (A = B).
Proof.
  refine (equiv_ap_inv issig_abgroup _ _ oE _).
  About equiv_path_sigma_hprop.
  refine (equiv_path_sigma_hprop _ _ oE _).
  exact equiv_path_group@{v u u u u u u u u u}.
Defined.

Definition equiv_path_abgroup_group `{Univalence} {A B : AbGroup}
  : (A = B :> AbGroup) <~> (A = B :> Group)
  := equiv_path_group@{v u u u u u u u u u} oE equiv_path_abgroup^-1.

(** ** Subgroups of abelian groups *)

(** Subgroups of abelian groups are abelian *)
Global Instance isabgroup_subgroup (G : AbGroup) (H : Subgroup G)
  : IsAbGroup H.
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intros x y.
  apply path_sigma_hprop.
  cbn. apply commutativity.
Defined.

Global Instance isnormal_ab_subgroup (G : AbGroup) (H : Subgroup G)
  : IsNormalSubgroup H.
Proof.
  intros x y; unfold in_cosetL, in_cosetR.
  refine (_ oE equiv_subgroup_inverse _ _).
  rewrite negate_sg_op.
  rewrite negate_involutive.
  by rewrite (commutativity (-y) x).
Defined.

(** ** Quotients of abelian groups *)

Global Instance isabgroup_quotient (G : AbGroup) (H : Subgroup G)
  : IsAbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)).
Proof.
  nrapply Build_IsAbGroup.
  1: exact _.
  intro x.
  srapply Quotient_ind_hprop.
  intro y; revert x.
  srapply Quotient_ind_hprop.
  intro x.
  apply (ap (tr o coeq)).
  apply commutativity.
Defined.

Definition QuotientAbGroup (G : AbGroup) (H : Subgroup G) : AbGroup
  := (Build_AbGroup (QuotientGroup' G H (isnormal_ab_subgroup G H)) _).

Theorem equiv_quotient_abgroup_ump {F : Funext} {G : AbGroup}
  (N : Subgroup G) (H : Group)
  : {f : GroupHomomorphism G H & forall (n : G), N n -> f n = mon_unit}
    <~> (GroupHomomorphism (QuotientAbGroup G N) H).
Proof.
  exact (equiv_grp_quotient_ump (Build_NormalSubgroup G N _) _).
Defined.

(** ** The wild category of abelian groups *)

Global Instance isgraph_abgroup : IsGraph AbGroup
  := isgraph_induced abgroup_group.

Global Instance is01cat_abgroup : Is01Cat AbGroup
  := is01cat_induced abgroup_group.

Global Instance is01cat_grouphomomorphism {A B : AbGroup} : Is01Cat (A $-> B)
  := is01cat_induced (@grp_homo_map A B).

Global Instance is0gpd_grouphomomorphism {A B : AbGroup} : Is0Gpd (A $-> B)
  := is0gpd_induced (@grp_homo_map A B).

Global Instance is2graph_abgroup : Is2Graph AbGroup
  := is2graph_induced abgroup_group.

(** AbGroup forms a 1Cat *)
Global Instance is1cat_abgroup : Is1Cat AbGroup
  := is1cat_induced _.

Global Instance hasmorext_abgroup `{Funext} : HasMorExt AbGroup
  := hasmorext_induced _.

Global Instance hasequivs_abgroup : HasEquivs AbGroup
  := hasequivs_induced _.

(** Zero object of AbGroup *)

Definition abgroup_trivial : AbGroup.
Proof.
  rapply (Build_AbGroup grp_trivial).
  by intros [].
Defined.

(** AbGroup is a pointed category *)
Global Instance ispointedcat_abgroup : IsPointedCat AbGroup.
Proof.
  snrapply Build_IsPointedCat.
  1: exact abgroup_trivial.
  { intro A.
    snrefine (Build_GroupHomomorphism (fun _ => mon_unit); _).
    1: exact _.
    { intros [] [].
      symmetry.
      apply left_identity. }
    intros g []; cbn.
    exact (grp_homo_unit g). }
  intro A.
  snrefine (Build_GroupHomomorphism (fun _ => mon_unit); _).
  1: exact _.
  { intros x y; symmetry.
    apply left_identity. }
  intros g x; cbn.
  apply path_unit.
Defined.

(** Image of group homomorphisms between abelian groups *)
Definition abgroup_image {A B : AbGroup} (f : A $-> B) : AbGroup
  := Build_AbGroup (grp_image f) _.

(** First isomorphism theorem of abelian groups *)
Definition abgroup_first_iso `{Funext} {A B : AbGroup} (f : A $-> B)
  : GroupIsomorphism (QuotientAbGroup A (grp_kernel f)) (abgroup_image f).
Proof.
  etransitivity.
  2: rapply grp_first_iso.
  apply grp_iso_quotient_normal.
Defined.

(** ** Biproducts of abelian groups *)

Definition ab_biprod (A B : AbGroup) : AbGroup.
Proof.
  rapply (Build_AbGroup (grp_prod A B)).
  intros [a b] [a' b'].
  apply path_prod; simpl; apply commutativity.
Defined.

(** These inherit [IsEmbedding] instances from their [grp_prod] versions. *)
Definition ab_biprod_inl {A B : AbGroup} : A $-> ab_biprod A B := grp_prod_inl.
Definition ab_biprod_inr {A B : AbGroup} : B $-> ab_biprod A B := grp_prod_inr.

(** Recursion principle *)
Proposition ab_biprod_rec {A B Y : AbGroup}
            (f : A $-> Y) (g : B $-> Y)
  : (ab_biprod A B) $-> Y.
Proof.
  snrapply Build_GroupHomomorphism.
  - intros [a b]; exact (f a + g b).
  - intros [a b] [a' b']; simpl.
    rewrite (grp_homo_op f).
    rewrite (grp_homo_op g).
    rewrite (associativity _ (g b) _).
    rewrite <- (associativity _ (f a') _).
    rewrite (commutativity (f a') _).
    rewrite (associativity _ (g b) _).
    exact (associativity _ (f a') _)^.
Defined.

(** These inherit [IsSurjection] instances from their [grp_prod] versions. *)
Definition ab_biprod_pr1 {A B : AbGroup} : ab_biprod A B $-> A := grp_prod_pr1.
Definition ab_biprod_pr2 {A B : AbGroup} : ab_biprod A B $-> B := grp_prod_pr2.

Corollary ab_biprod_rec_uncurried {A B Y : AbGroup}
  : (A $-> Y) * (B $-> Y)
    -> (ab_biprod A B) $-> Y.
Proof.
  intros [f g]. exact (ab_biprod_rec f g).
Defined.

Proposition ab_biprod_rec_beta' {A B Y : AbGroup}
            (u : ab_biprod A B $-> Y)
  : ab_biprod_rec (u $o ab_biprod_inl) (u $o ab_biprod_inr) == u.
Proof.
  intros [a b]; simpl.
  refine ((grp_homo_op u _ _)^ @ ap u _).
  apply path_prod.
  - exact (right_identity a).
  - exact (left_identity b).
Defined.

Proposition ab_biprod_rec_beta `{Funext} {A B Y : AbGroup}
            (u : ab_biprod A B $-> Y)
  : ab_biprod_rec (u $o ab_biprod_inl) (u $o ab_biprod_inr) = u.
Proof.
  apply equiv_path_grouphomomorphism.
  exact (ab_biprod_rec_beta' u).
Defined.

Proposition ab_biprod_rec_inl_beta `{Funext} {A B Y : AbGroup}
            (a : A $-> Y) (b : B $-> Y)
  : (ab_biprod_rec a b) $o ab_biprod_inl = a.
Proof.
  apply equiv_path_grouphomomorphism.
  intro x; simpl.
  rewrite (grp_homo_unit b).
  exact (right_identity (a x)).
Defined.

Proposition ab_biprod_rec_inr_beta `{Funext} {A B Y : AbGroup}
            (a : A $-> Y) (b : B $-> Y)
  : (ab_biprod_rec a b) $o ab_biprod_inr = b.
Proof.
  apply equiv_path_grouphomomorphism.
  intro y; simpl.
  rewrite (grp_homo_unit a).
  exact (left_identity (b y)).
Defined.

Theorem isequiv_ab_biprod_rec `{Funext} {A B Y : AbGroup}
  : IsEquiv (@ab_biprod_rec_uncurried A B Y).
Proof.
  srapply isequiv_adjointify.
  - intro phi.
    exact (phi $o ab_biprod_inl, phi $o ab_biprod_inr).
  - intro phi.
    exact (ab_biprod_rec_beta phi).
  - intros [a b].
    apply path_prod.
    + apply ab_biprod_rec_inl_beta.
    + apply ab_biprod_rec_inr_beta.
Defined.

(** Corecursion principle, inherited from Groups/Group.v. *)
Definition ab_biprod_corec {A B X : AbGroup}
           (f : X $-> A) (g : X $-> B)
  : X $-> ab_biprod A B := grp_prod_corec f g.

Definition ab_corec_beta {X Y A B : AbGroup} (f : X $-> Y) (g0 : Y $-> A) (g1 : Y $-> B)
  : ab_biprod_corec g0 g1 $o f $== ab_biprod_corec (g0 $o f) (g1 $o f)
  := fun _ => idpath.

(** *** Functoriality of [ab_biprod] *)

Definition functor_ab_biprod {A A' B B' : AbGroup} (f : A $-> A') (g: B $-> B')
  : ab_biprod A B $-> ab_biprod A' B'
  := (ab_biprod_corec (f $o ab_biprod_pr1) (g $o ab_biprod_pr2)).

Definition ab_biprod_functor_beta {Z X Y A B : AbGroup} (f0 : Z $-> X) (f1 : Z $-> Y)
           (g0 : X $-> A) (g1 : Y $-> B)
  : functor_ab_biprod g0 g1 $o ab_biprod_corec f0 f1
                      $== ab_biprod_corec (g0 $o f0) (g1 $o f1)
  := fun _ => idpath.

Definition isequiv_functor_ab_biprod {A A' B B' : AbGroup}
           (f : A $-> A') (g : B $-> B') `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : IsEquiv (functor_ab_biprod f g).
Proof.
  srapply isequiv_adjointify.
  1: { rapply functor_ab_biprod;
       apply grp_iso_inverse.
       + exact (Build_GroupIsomorphism _ _ f _).
       + exact (Build_GroupIsomorphism _ _ g _). }
  all: intros [a b]; simpl.
  all: apply path_prod'.
  1,2: apply eisretr.
  all: apply eissect.
Defined.

Definition equiv_functor_ab_biprod {A A' B B' : AbGroup}
           (f : A $-> A') (g : B $-> B') `{IsEquiv _ _ f} `{IsEquiv _ _ g}
  : GroupIsomorphism (ab_biprod A B) (ab_biprod A' B')
  := Build_GroupIsomorphism _ _ _ (isequiv_functor_ab_biprod f g).

(** ** Kernels of abelian groups *)

Definition ab_kernel {A B : AbGroup} (f : A $-> B) : AbGroup
  := Build_AbGroup (grp_kernel f) _.

(** ** Transporting in families related to abelian groups *)

Lemma transport_abgrouphomomorphism_from_const `{Univalence} {A B B' : AbGroup}
      (p : B = B') (f : GroupHomomorphism A B)
  : transport (Hom A) p f
    = grp_homo_compose (equiv_path_abgroup^-1 p) f.
Proof.
  induction p.
  by apply equiv_path_grouphomomorphism.
Defined.

Lemma transport_abgrouphomomorphism_to_const `{Univalence} {A A' B : AbGroup}
      (p : A = A') (f : GroupHomomorphism A B)
  : transport (fun G => Hom G B) p f
    = grp_homo_compose f (grp_iso_inverse (equiv_path_abgroup^-1 p)).
Proof.
  induction p; cbn.
  by apply equiv_path_grouphomomorphism.
Defined.

(** ** Operations on abelian groups *)

(** The negation automorphism of an abelian group *)
Definition ab_homo_negation {A : AbGroup} : GroupIsomorphism A A.
Proof.
  snrapply Build_GroupIsomorphism.
  - snrapply Build_GroupHomomorphism.
    + exact (fun a => -a).
    + intros x y.
      refine (grp_inv_op x y @ _).
      apply commutativity.
  - srapply isequiv_adjointify.
    1: exact (fun a => -a).
    1-2: exact negate_involutive.
Defined.

(** Addition [+] is a group homomorphism [A+A -> A]. *)
Definition ab_add_homo {A : AbGroup}
  : ab_biprod A A $-> A
  := ab_biprod_rec grp_homo_id grp_homo_id.

(** We can add group homomorphisms. *)
Definition ab_homo_add {A : Group} {B : AbGroup} (f g : A $-> B)
  : A $-> B.
Proof.
  refine (grp_homo_compose ab_add_homo _).
  (** [fun a => f(a) + g(a)] **)
  exact (grp_prod_corec f g).
Defined.
