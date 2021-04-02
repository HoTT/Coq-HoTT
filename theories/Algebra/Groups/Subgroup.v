Require Import Basics Types HProp HSet HFiber PathAny WildCat.
Require Import Algebra.Groups.Group.

Local Open Scope mc_mult_scope.
Generalizable Variables G H A B C N f g.

(** * Subgroups *)

(** The property of being a subgroup *)
Class IsSubgroup {G : Group} (H : G -> Type) := {
  ishprop_issubgroup : forall x, IsHProp (H x) ;
  issubgroup_unit : H mon_unit ;
  issubgroup_op : forall x y, H x -> H y -> H (x * y) ;
  issubgroup_inv : forall x, H x -> H (- x) ;
(*   issubgroup_incl : GroupHomomorphism G H; *)
(*   isinj_issubgroup_incl : IsInjective issubgroup_incl; *)
}.

Global Existing Instance ishprop_issubgroup.
(* Global Existing Instance isinj_issubgroup_incl. *)
(*
(* Subgroup inclusion is an embedding. *)
Global Instance isembedding_issubgroup_incl `{!IsSubgroup G H}
  : IsEmbedding (@issubgroup_incl G H _).
Proof.
  apply isembedding_isinj_hset.
  apply isinj_issubgroup_incl.
Defined. *)

Definition issig_issubgroup {G : Group} (H : G -> Type) : _ <~> IsSubgroup H
  := ltac:(issig).

Global Instance ishset_issubgroup `{F : Funext} {G : Group} {H : G -> Type}
  : IsHProp (IsSubgroup H).
Proof.
  exact (trunc_equiv' _ (issig_issubgroup H)).
Defined.

Record Subgroup (G : Group) := {
  subgroup_pred : G -> Type ;
  subgroup_issubgroup : IsSubgroup subgroup_pred ;
}.

Coercion subgroup_pred : Subgroup >-> Funclass.
Global Existing Instance subgroup_issubgroup.

Definition subgroup_unit `(H : Subgroup G) : H mon_unit := issubgroup_unit.
Definition subgroup_inv `(H : Subgroup G) x : H x -> H (- x) := issubgroup_inv x.
Definition subgroup_op `(H : Subgroup G) x y : H x -> H y -> H (x * y)
:= issubgroup_op x y.

(** The group given by a subgroup *)
Definition subgroup_group (G : Group) (H : Subgroup G) : Group.
Proof.
  snrefine (
    Build_Group
      (** The underlying type is the sigma type of the predicate. *)
      (sig H)
      (** The operation is the group operation on the first projection with the proof  of being in the subgroup given by the subgroup data. *)
      (fun '(x ; p) '(y ; q) => (x * y ; issubgroup_op x y p q))
      (** The unit *)
      (mon_unit ; issubgroup_unit)
      (** Inverse *)
      (fun '(x ; p) => (- x ; issubgroup_inv _ p))
      _).
 (** Why isn't typeclasses able to pick these up earlier (without snrefine ofc)?? *)
  1-3: exact _.
  (** Finally we need to prove our group laws. *)
  repeat split.
  1: exact _.
  all: grp_auto.
Defined.

Coercion subgroup_group : Subgroup >-> Group.

Definition subgroup_incl {G : Group} (H : Subgroup G)
  : GroupHomomorphism (subgroup_group G H) G.
Proof.
  snrapply Build_GroupHomomorphism'.
  1: exact pr1.
  repeat split.
Defined.

Global Instance isembedding_subgroup_incl {G : Group} (H : Subgroup G)
  : IsEmbedding (subgroup_incl H)
  := fun _ => trunc_equiv' _ (hfiber_fibration _ _).

Definition issig_subgroup {G : Group} : _ <~> Subgroup G
  := ltac:(issig).

(* Definition issig_subgroup' `{Univalence} {G : Group}
  : {h : G -> hProp & IsSubgroup h} <~> Subgroup G.
Proof.
  snrapply equiv_adjointify.
  { intros [h p].
    exact (Build_Subgroup G h p). }
  { intros [h p].
    exists (fun g => BuildTruncType (-1) (h g)).
    exact _. }
  1: intro x; reflexivity.
  simpl.
  hnf.
  intros [h p].
  srapply path_sigma.
  1: funext x; rapply TruncType.path_iff_hprop; trivial.
  rewrite trans *)
  


(** Trivial subgroup *)
Definition trivial_subgroup {G} : Subgroup G.
Proof.
  rapply (Build_Subgroup G (fun x => x = mon_unit)).
  rapply Build_IsSubgroup.
  1: reflexivity.
  { intros x y p q.
    rewrite p, q.
    apply left_identity. }
  intros x p.
  rewrite p.
  apply negate_mon_unit.
Defined.

(** Every group is a subgroup of itself *)
(**  The maximal subgroup *)
Definition maximal_subgroup {G} : Subgroup G.
Proof.
  rapply (Build_Subgroup G (fun x => Unit)).
  split; auto; exact _.
Defined.

(* (** Paths between subgroups correspond to isomorphisms respecting the inclusions. *)
Proposition equiv_path_subgroup `{F : Funext} {G : Group} (H K : Subgroup G)
  : (exists p : GroupIsomorphism H K, subgrp_incl H G = (subgrp_incl K G) $o p)
      <~> H = K.
Proof.
  refine (equiv_ap_inv (@issig_subgroup' G) H K oE _).
  refine ((equiv_path_sigma _ _ _) oE _); cbn.
  refine (equiv_functor_sigma' equiv_path_group _).
  intro phi.
  refine (equiv_concat_l (transport_sigma _ _) _ oE _).
  refine (equiv_path_sigma_hprop _ _ oE _); unfold pr1.
  refine (equiv_concat_l (transport_lemma _ _) _ oE _).
  rewrite (eissect equiv_path_group phi).
  refine ((equiv_ap' (equiv_precompose_cat_equiv phi) _ _)^-1%equiv oE _); cbn.
  apply equiv_concat_l.
  apply equiv_path_grouphomomorphism; intro x; cbn.
  rewrite (eissect phi x).
  reflexivity.
Defined. *)

Global Instance ishset_subgroup `{Funext} {G : Group} : IsHSet (Subgroup G).
Proof.
  refine (trunc_equiv' _ issig_subgroup).
  rapply trunc_sigma.
  

(*   refine (trunc_equiv' _ (equiv_ap' issig_subgroup^-1 _ _)^-1). *)
Admitted.
(*
Corollary ishprop_path_subgroup `{U : Univalence} {G : Group} {H K : Subgroup G}
  : IsHProp (H = K).
Proof.
  refine (trunc_equiv' _ (equiv_ap' issig_subgroup^-1%equiv _ _)^-1%equiv).
  
  apply istrunc_paths.
  
  exact _.
  rapply (equiv_transport IsHProp _ _).
  - apply equiv_path_universe.
    exact (equiv_path_subgroup H K).
  - apply equiv_hprop_allpath.
    intros [f p] [g q].
    apply path_sigma_hprop; cbn.
    apply equiv_path_groupisomorphism.
    apply ap10.
    rapply (ismono_isinj (subgrp_incl K G) (isinj_issubgroup_incl)); cbn.
    exact (ap (grp_homo_map H G) (p^ @ q)).
Defined.

(** Any group has as set of subgroups. *)
Corollary ishset_subgroup `{U: Univalence} {G : Group}
  : IsHSet (Subgroup G).
Proof.
  intros H K; apply ishprop_path_subgroup.
Defined.
*)
Section Cosets.

  (** Left and right cosets give equivalence relations. *)

  Context {G : Group} (H : Subgroup G).

  (** The relation of being in a left coset represented by an element. *)
  Definition in_cosetL : Relation G := fun x y => hfiber (subgroup_incl H) (-x * y).
  (** The relation of being in a right coset represented by an element. *)
  Definition in_cosetR : Relation G := fun x y => hfiber (subgroup_incl H) (x * -y).
  (** These are props *)
  Global Instance ishprop_in_cosetL : is_mere_relation G in_cosetL := _.
  Global Instance ishprop_in_cosetR : is_mere_relation G in_cosetR := _.
  (** In fact, they are both equivalence relations. *)
  Global Instance reflexive_in_cosetL : Reflexive in_cosetL.
  Proof.
    intro x; hnf.
    exists mon_unit.
    refine (_ @ _).
    2: apply symmetry, left_inverse.
    apply grp_homo_unit.
  Defined.

  Global Instance reflexive_in_cosetR : Reflexive in_cosetR.
  Proof.
    intro x; hnf.
    exists mon_unit.
    refine (_ @ _).
    2: apply symmetry, right_inverse.
    apply grp_homo_unit.
  Defined.

  Global Instance symmetric_in_cosetL : Symmetric in_cosetL.
  Proof.
    intros x y [h p]; hnf.
    exists (-h).
    refine (_ @ _).
    1: apply grp_homo_inv.
    apply moveR_equiv_M.
    refine (p @ _).
    symmetry.
    refine (negate_sg_op _ _ @ _).
    refine (ap (-x *.) _).
    apply negate_involutive.
  Defined.

  Global Instance symmetric_in_cosetR : Symmetric in_cosetR.
  Proof.
    intros x y [h p]; hnf.
    exists (-h).
    refine (_ @ _).
    1: apply grp_homo_inv.
    apply moveR_equiv_M.
    refine (p @ _).
    symmetry.
    refine (negate_sg_op _ _ @ _).
    refine (ap (fun x => x *  -y) _).
    apply negate_involutive.
  Defined.

  Global Instance transitive_in_cosetL : Transitive in_cosetL.
  Proof.
    intros x y z [h p] [h' q].
    exists (h * h').
    refine (grp_homo_op _ _ _ @ _).
    destruct p^, q^.
    rewrite <- simple_associativity.
    apply ap.
    rewrite simple_associativity.
    refine (ap (fun x => x *  -z) _ @ _).
    1: apply right_inverse.
    apply left_identity.
  Defined.

  Global Instance transitive_in_cosetR : Transitive in_cosetR.
  Proof.
    intros x y z [h p] [h' q].
    exists (h * h').
    refine (grp_homo_op _ _ _ @ _).
    destruct p^, q^.
    rewrite <- simple_associativity.
    apply ap.
    rewrite simple_associativity.
    refine (ap (fun x => x *  -z) _ @ _).
    1: apply left_inverse.
    apply left_identity.
  Defined.

End Cosets.

(** Identities related to the left and right cosets. *)

Definition in_cosetL_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetL N (-x * y) mon_unit <~> in_cosetL N x y.
Proof.
  intros x y.
  unfold in_cosetL.
  rewrite negate_sg_op.
  rewrite negate_involutive.
  rewrite (right_identity (-y * x)).
  change (in_cosetL N y x <~> in_cosetL N x y).
  srapply equiv_iff_hprop;
  by intro; symmetry.
Defined.

Definition in_cosetR_unit {G : Group} {N : Subgroup G}
  : forall x y, in_cosetR N (x * -y) mon_unit <~> in_cosetR N x y.
Proof.
  intros x y.
  unfold in_cosetR.
  rewrite negate_mon_unit.
  rewrite (right_identity (x * -y)).
  reflexivity.
Defined.

(** Symmetry is an equivalence. *)
Definition equiv_in_cosetL_symm {G : Group} {N : Subgroup G}
  : forall x y, in_cosetL N x y <~> in_cosetL N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

Definition equiv_in_cosetR_symm {G : Group} {N : Subgroup G}
  : forall x y, in_cosetR N x y <~> in_cosetR N y x.
Proof.
  intros x y.
  srapply equiv_iff_hprop.
  all: by intro.
Defined.

(* A subgroup is normal if being in a left coset is equivalent to being in a right coset represented by the same element. *)
Class IsNormalSubgroup {G : Group} (N : Subgroup G)
  := isnormal : forall {x y}, in_cosetL N x y <~> in_cosetR N x y.

Record NormalSubgroup (G : Group) := {
  normalsubgroup_subgroup : Subgroup G ;
  normalsubgroup_isnormal : IsNormalSubgroup normalsubgroup_subgroup ;
}.

Coercion normalsubgroup_subgroup : NormalSubgroup >-> Subgroup.
Global Existing Instance normalsubgroup_isnormal.

(* Inverses are then respected *)
Definition in_cosetL_inv {G : Group} {N : Subgroup G} `{!IsNormalSubgroup N}
  : forall x y : G, in_cosetL N (-x) (-y) <~> in_cosetL N x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetL_unit _ _)^-1).
  refine (_ oE isnormal).
  refine (_ oE in_cosetR_unit _ _).
  refine (_ oE isnormal^-1).
  by rewrite negate_involutive.
Defined.

Definition in_cosetR_inv {G : Group} {N : Subgroup G} `{!IsNormalSubgroup N}
  : forall x y : G, in_cosetR N (-x) (-y) <~> in_cosetR N x y.
Proof.
  intros x y.
  refine (_ oE (in_cosetR_unit _ _)^-1).
  refine (_ oE isnormal^-1).
  refine (_ oE in_cosetL_unit _ _).
  refine (_ oE isnormal).
  by rewrite negate_involutive.
Defined.

(** There is always another element of the normal subgroup allowing us to commute with an element of the group. *)
Definition normal_subgroup_swap {G : Group} {N : Subgroup G} `{!IsNormalSubgroup N}
  (x : G) (h : N)
  : exists h' : N, x * subgroup_incl N h = subgroup_incl N h' * x.
Proof.
  assert (X : in_cosetL N x (x * subgroup_incl _ h)).
  { exists h.
    rewrite simple_associativity.
    rewrite left_inverse.
    symmetry.
    apply left_identity. }
  apply isnormal in X.
  destruct X as [a p].
  rewrite negate_sg_op in p.
  rewrite simple_associativity in p.
  eexists (-a).
  symmetry.
  rewrite grp_homo_inv.
  apply (moveR_equiv_M (f := (- _ *.))).
  cbn; rewrite negate_involutive.
  rewrite simple_associativity.
  apply (moveL_equiv_M (f := (fun x => x * _))).
  apply (moveL_equiv_M (f := (fun x => x * _))).
  symmetry.
  assumption.
Defined.

(* This lets us prove that left and right coset relations are congruences. *)
Definition in_cosetL_cong {G : Group} {N : Subgroup G} `{!IsNormalSubgroup N}
  (x x' y y' : G)
  : in_cosetL N x y -> in_cosetL N x' y' -> in_cosetL N (x * x') (y * y').
Proof.
  intros [a p] [b q].
  eexists ?[c].
  rewrite negate_sg_op.
  rewrite <- simple_associativity.
  rewrite (simple_associativity (-x) y).
  rewrite <- p.
  rewrite simple_associativity.
  rewrite (normal_subgroup_swap _ a).2.
  rewrite <- simple_associativity.
  rewrite <- q.
  apply grp_homo_op.
Defined.

Definition in_cosetR_cong  {G : Group} {N : Subgroup G} `{!IsNormalSubgroup N}
  (x x' y y' : G)
  : in_cosetR N x y -> in_cosetR N x' y' -> in_cosetR N (x * x') (y * y').
Proof.
  intros [a p] [b q].
  eexists ?[c].
  rewrite negate_sg_op.
  rewrite <- simple_associativity.
  rewrite (simple_associativity x' (-y')).
  rewrite <- q.
  rewrite simple_associativity.
  rewrite (normal_subgroup_swap _ b).2.
  rewrite <- simple_associativity.
  rewrite <- p.
  apply grp_homo_op.
Defined.

Definition isnormalsubgroup_of_cong_mem  {G : Group} {N : Subgroup G}
  (h : forall (g : G) (n : N), exists m : N,
    - g * subgroup_incl N n * g = subgroup_incl N m)
  : IsNormalSubgroup N.
Proof.
  intros x y.
  apply equiv_iff_hprop; intros [m p].
  1: specialize (h (-y) (-m)).
  2: specialize (h y (-m)).
  1-2: destruct h as [m' p'].
  1-2: exists m'.
  1-2: rewrite <- p'.
  1-2: f_ap.
  1-2: rewrite grp_homo_inv, p, negate_sg_op, involutive. 
  1: rewrite associativity, involutive, (negate_r G y).
  2: rewrite (associativity (-y)), (negate_l G y).
  1-2: rewrite (left_identity _); reflexivity.
Defined.
