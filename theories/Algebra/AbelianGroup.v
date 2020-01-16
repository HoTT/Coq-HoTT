Require Import HoTT.Basics HoTT.Types UnivalenceImpliesFunext.
Require Import Truncations.
Require Import HIT.Coeq.
Require Import Algebra.Group.
Require Import Algebra.Subgroup.
Require Import Cubical.
Import TrM.

Local Open Scope mc_mult_scope.

(** * Abelian groups *)

(** Definition of an abelian group *)

Class AbGroup := {
  abgroup_type : Type;
  abgroup_sgop :> SgOp abgroup_type;
  abgroup_unit :> MonUnit abgroup_type;
  abgroup_inverse :> Negate abgroup_type;
  abgroup_isabgroup :> IsAbGroup abgroup_type;
}.

(** We want abelian groups to be coerced to the underlying type. *)
Coercion abgroup_type : AbGroup >-> Sortclass.

(** The underlying group of an abelian group. *)
Definition group_abgroup : AbGroup -> Group.
Proof.
  intros [G ? ? ? [l ?]].
  ntc_rapply (Build_Group G _ _ _ l).
Defined.

(** We also want abelian groups to be coerced to the underlying group. *)
Coercion group_abgroup : AbGroup >-> Group.

(** Definition of Abelianization.

  Given a map F that turns any group into an abelian group, and a unit homomorphism eta_X : X -> F X. This data is considered an Abelianization if and only if for all maps X -> A, there exists a unique g such that h == g o eta X. *)
Definition IsAbelianization {G : Group} (G_ab : AbGroup)
  (eta : GroupHomomorphism G G_ab)
  := forall (A : AbGroup) (h : GroupHomomorphism G A),
    Contr (exists (g : GroupHomomorphism G_ab A), h == g o eta).

Existing Class IsAbelianization.

(** Here we define abelianization as a HIT. Specifically as a set-coequalizer of the following to maps: (a, b, c) |-> a (b c) and (a, b, c) |-> a (c b).

From this we can show that Abel G is an abelian group.

In fact this models the following HIT:

HIT Abel (G : Group) := 
 | ab : G -> Abel G
 | ab_comm : forall x y z, ab (x * (y * z)) = ab (x * (z * y)).

We also derive ab and ab_comm from our coequalizer definition, and even prove the induction and computation rules for this HIT.

This HIT was suggested by Dan Christensen.
*)

Section Abel.

  (** Let G be a group. *)
  Context (G : Group).

  (** We locally define a map uncurry2 that lets us uncurry A * B * C -> D twice. *)
  Local Definition uncurry2 {A B C D : Type}
    : (A -> B -> C -> D) -> A * B * C -> D.
  Proof.
    intros f [[a b] c].
    by apply f.
  Defined.

  (** The type Abel is defined to be the set coequalizer of the following maps G^3 -> G. *)
  Definition Abel
    := Tr 0 (Coeq
      (uncurry2 (fun a b c => a * (b * c)))
      (uncurry2 (fun a b c => a * (c * b)))).

  (** We have a natural map from G to Abel G *)
  Definition ab : G -> Abel.
  Proof.
    intro g.
    apply tr, coeq, g.
  Defined.

  (** This map has to satisfy the condition ab_comm *)
  Definition ab_comm a b c
    : ab (a * (b * c)) = ab (a * (c * b)).
  Proof.
    apply (ap tr).
    exact (cglue (a, b, c)).
  Defined.

  (** It is clear that Abel is a set. *)
  Global Instance istrunc_abel : IsHSet Abel := _.

  (** We can derive the induction principle from the ones for truncation and the coequalizer. *)
  Definition Abel_ind (P : Abel -> Type) `{forall x, IsHSet (P x)} 
    (a : forall x, P (ab x)) (c : forall x y z, DPath P (ab_comm x y z)
      (a (x * (y * z))) (a (x * (z * y))))
    : forall (x : Abel), P x.
  Proof.
    serapply Trunc_ind.
    serapply Coeq_ind.
    1: apply a.
    intros [[x y] z].
    refine (transport_compose _ _ _ _ @ _).
    serapply dp_path_transport^-1.
    apply c.
  Defined.

  (** The computation rule can also be prove. *)
  Definition Abel_ind_beta_ab_comm (P : Abel -> Type)
    `{forall x, IsHSet (P x)}(a : forall x, P (ab x))
    (c : forall x y z, DPath P (ab_comm x y z)
      (a (x * (y * z))) (a (x * (z * y))))
    (x y z : G) : dp_apD (Abel_ind P a c) (ab_comm x y z) = c x y z.
  Proof.
    unfold ab_comm.
    apply dp_apD_path_transport.
    rewrite (apD_compose' tr).
    rewrite (Coeq_ind_beta_cglue _ _ _ (x, y, z)).
    unfold Abel_ind.
    refine (_ @ concat_1p _).
    refine (concat_p_pp _ _ _ @ _).
    apply whiskerR.
    apply concat_Vp.
  Defined.

  (** We also have a recursion princple. *)
  Definition Abel_rec (P : Type) `{IsHSet P} (a : G -> P)
    (c : forall x y z, a (x * (y * z)) = a (x * (z * y)))
    : Abel -> P.
  Proof.
    apply (Abel_ind _ a).
    intros; apply dp_const, c.
  Defined.

  (** Here is a simpler version of Abel_ind when our target is a HProp. This lets us discard all the higher paths. *)
  Definition Abel_ind_hprop (P : Abel -> Type) `{forall x, IsHProp (P x)} 
    (a : forall x, P (ab x)) : forall (x : Abel), P x.
  Proof.
    serapply (Abel_ind _ a).
    intros; apply dp_path_transport.
    apply path_ishprop.
  Defined.

  (** And its recursion version. *)
  Definition Abel_rec_hprop (P : Type) `{IsHProp P}
    (a : G -> P) : Abel -> P.
  Proof.
    apply (Abel_rec _ a).
    intros; apply path_ishprop.
  Defined.

End Abel.

(** We make sure that G is implicit in the arguments of ab and ab_comm. *)
Arguments ab {_}.
Arguments ab_comm {_}.

(** Now we can show that Abel G is infact an abelian group. *)

Section AbelGroup.

  Context `{Funext} (G : Group).

  (** Firstly we derive the operation on Abel G. This is defined as follows:
        ab x + ab y := ab (x y)
      But we need to also check that it preserves ab_comm in the appropriate way. *)
  Global Instance abel_sgop : SgOp (Abel G).
  Proof.
    serapply Abel_rec.
    { intro a.
      serapply Abel_rec.
      { intro b.
        exact (ab (a * b)). }
      intros b c d; cbn.
      refine (ab_comm _ _ _ @ _).
      refine (ap _ _ @ _).
      { refine (ap _ (associativity _ _ _)^ @ _).
        refine (associativity _ _ _). }
      refine (ab_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _)^ @ _).
      refine (ab_comm _ _ _ @ _).
      refine (ap _ (ap _ (associativity _ _ _)^)). }
    intros a b c.
    apply path_forall.
    serapply Abel_ind_hprop.
    cbn; intro d.
    refine (ap _ (associativity _ _ _)^ @ _).
    refine (ap _ (ap _ (associativity _ _ _)^) @ _).
    refine (ab_comm _ _ _ @ _).
    refine (ap _ (ap _ (associativity _ _ _)^) @ _).
    refine (ap _ (associativity _ _ _) @ _).
    refine (ab_comm _ _ _ @ _).
    refine (ap _ (associativity _ _ _)^ @ _).
    refine (ap _ (ap _ (associativity _ _ _)) @ _).
    refine (ap _ (associativity _ _ _)).
  Defined.

  (** We can now easily show that this operation is associative by associativity in G and the fact that being associative is a proposition. *)
  Global Instance abel_sgop_associative : Associative abel_sgop.
  Proof.
    serapply Abel_ind_hprop; intro x.
    serapply Abel_ind_hprop; intro y.
    serapply Abel_ind_hprop; intro z.
    cbn; apply ap, associativity.
  Defined.

  (** From this we know that Abel G is a semigroup. *)
  Global Instance abel_issemigroup : IsSemiGroup (Abel G) := {}.

  (** We define the unit as ab of the unit of G *)
  Global Instance abel_mon_unit : MonUnit (Abel G) := ab mon_unit.

  (** By using Abel_ind_hprop we can prove the left and right identity laws. *)
  Global Instance abel_leftidentity : LeftIdentity abel_sgop abel_mon_unit.
  Proof.
    serapply Abel_ind_hprop; intro x.
    cbn; apply ap, left_identity.
  Defined.

  Global Instance abel_rightidentity : RightIdentity abel_sgop abel_mon_unit.
  Proof.
    serapply Abel_ind_hprop; intro x.
    cbn; apply ap, right_identity.
  Defined.

  (** Hence Abel G is a monoid *)
  Global Instance ismonoid_abel : IsMonoid (Abel G) := {}.

  (** We can also prove that the operation is commutative! This will come in handy later. *)
  Global Instance abel_commutative : Commutative abel_sgop.
  Proof.
    serapply Abel_ind_hprop; intro x.
    serapply Abel_ind_hprop; intro y.
    cbn.
    rewrite <- (left_identity (x * y)).
    rewrite <- (left_identity (y * x)).
    apply ab_comm.
  Defined.

  (** Now we can define the negation. This is just
        - (ab g) := (ab (g^-1) 
      However when checking that it respects ab_comm we have to show the following:
        ab (- z * - y * - x) = ab (- y * - z * - x)
      there is no obvious way to do this, but we note that ab (x * y) is exactly the definition of ab x + ab y! Hence by commutativity we can show this. *)
  Global Instance abel_negate : Negate (Abel G).
  Proof.
    serapply Abel_rec.
    { intro g.
      exact (ab (-g)). }
    intros x y z; cbn.
    rewrite ?negate_sg_op.
    change (ab(- z) * ab(- y) * ab (- x) = ab (- y) * ab (- z) * ab(- x)).
    by rewrite (commutativity (ab (-z)) (ab (-y))).
  Defined.

  (** Again by Abel_ind_hprop and the corresponding laws for G we can prove the left and right inverse laws. *)
  Global Instance abel_leftinverse : LeftInverse abel_sgop abel_negate abel_mon_unit.
  Proof.
    serapply Abel_ind_hprop; intro x.
    cbn; apply ap; apply left_inverse.
  Defined.

  Instance abel_rightinverse : RightInverse abel_sgop abel_negate abel_mon_unit.
  Proof.
    serapply Abel_ind_hprop; intro x.
    cbn; apply ap; apply right_inverse.
  Defined.

  (** Thus Abel G is a group *)
  Global Instance isgroup_abel : IsGroup (Abel G) := {}.

  (** And since the operation is commutative and abelian group. *)
  Global Instance isabgroup_abel : IsAbGroup (Abel G) := {}.

  (** By definition, the map ab is also a group homomorphism. *)
  Global Instance issemigrouppreserving_ab : IsSemiGroupPreserving ab.
  Proof.
    by unfold IsSemiGroupPreserving.
  Defined.

End AbelGroup.

(** We can easily prove that ab is a surjection. *)
Global Instance issurj_ab `{Funext} {G : Group} : IsSurjection ab.
Proof.
  serapply Abel_ind_hprop.
  intro x; cbn.
  exists (tr (x; @idpath _ (ab x))).
  apply path_ishprop.
Defined.

(** Now we finally check that our definition of abelianization satisfies the universal property of being an abelianization. *)
Section Abelianization.

  Context `{Funext}.

  (** We define abel to be the abelianization of a group. This is a map from Group to AbGroup. *)
  Definition abel : Group -> AbGroup.
  Proof.
    intro G.
    serapply (Build_AbGroup (Abel G)).
  Defined.

  (** The unit of this map is the map ab which typeclasses can pick up to be a homomorphism. We write it out explicitly here. *)
  Definition abel_unit (X : Group)
    : GroupHomomorphism X (abel X).
  Proof.
    simple notypeclasses refine (Build_GroupHomomorphism _).
    + exact ab.
    + exact _.
  Defined.

  (** Finally we can prove that our construction abel is an abelianization. *)
  Global Instance isabelianization_abel {G : Group}
    : IsAbelianization (abel G) (abel_unit G).
  Proof.
    intros A h.
    serapply Build_Contr.
    { srefine (_;_).
      { simple notypeclasses refine (Build_GroupHomomorphism _).
        { serapply (Abel_rec _ _ h).
          intros x y z.
          refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
          apply (ap (_ *.)).
          refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
          apply commutativity. }
        serapply Abel_ind_hprop; intro x.
        serapply Abel_ind_hprop; intro y.
        apply grp_homo_op. }
      cbn; reflexivity. }
    intros [g p].
    apply path_sigma_hprop; cbn.
    apply equiv_path_grouphomomorphism.
    serapply Abel_ind_hprop.
    exact p.
  Defined.

End Abelianization.

Theorem groupiso_isabelianization {G : Group}
  (A B : AbGroup)
  (eta1 : GroupHomomorphism G A)
  (eta2 : GroupHomomorphism G B)
  {x : IsAbelianization A eta1}
  {y : IsAbelianization B eta2}
  : GroupIsomorphism A B.
Proof.
  unfold IsAbelianization in x, y.
  destruct (x B eta2) as [[a ah] ac].
  destruct (y A eta1) as [[b bh] bc].
  destruct (x A eta1) as [[c ch] cc].
  destruct (y B eta2) as [[d dh] dc].
  serapply (Build_GroupIsomorphism _ _ a).
  serapply (isequiv_adjointify _ b).
  { apply ap10.
    change (@grp_homo_map _ _ (grp_homo_compose a b)
      = @grp_homo_map _ _ grp_homo_id).
    refine (ap (@grp_homo_map _ _) _).
    refine (ap pr1 ((dc (_; _))^ @ dc (grp_homo_id; _))).
    1: exact (fun i => ah i @ ap a (bh i)).
    reflexivity. }
  { apply ap10.
    change (@grp_homo_map _ _ (grp_homo_compose b a)
      = @grp_homo_map _ _ grp_homo_id).
    refine (ap (@grp_homo_map _ _) _).
    refine (ap pr1 ((cc (_; _))^ @ cc (grp_homo_id; _))).
    1: exact (fun i => bh i @ ap b (ah i)).
    reflexivity. }
Defined.

Theorem homotopic_isabelianization {G : Group} (A B : AbGroup)
  (eta1 : GroupHomomorphism G A) (eta2 : GroupHomomorphism G B)
  {x : IsAbelianization A eta1} {y : IsAbelianization B eta2}
  : eta2 == grp_homo_compose (groupiso_isabelianization A B eta1 eta2) eta1.
Proof.
  unfold IsAbelianization in x, y.
  destruct (x B eta2) as [[a ah] ac].
  destruct (y A eta1) as [[b bh] bc].
  refine (transport (fun e : GroupHomomorphism A B
    => _ == (fun x : G => e (eta1 x))) (ap pr1 (ac _)) ah).
Defined.

(** Hence any abelianization is surjective. *)
Global Instance issurj_isabelianization `{Funext} {G : Group}
  (A : AbGroup) (eta : GroupHomomorphism G A)
  : IsAbelianization A eta -> IsSurjection eta.
Proof.
  intros k.
  pose (homotopic_isabelianization A (abel G) eta (abel_unit G)) as p.
  refine (@cancelR_isequiv_conn_map _ _ _ _ _ _ _
    (conn_map_homotopic _ _ _ p _)).
Qed.

Global Instance isequiv_abgroup_abelianization `{U : Univalence}
  (A B : AbGroup) (eta : GroupHomomorphism A B) {H : IsAbelianization B eta}
  : IsEquiv eta.
Proof.
  destruct (H A grp_homo_id) as [[a ah] ac].
  serapply (isequiv_adjointify eta a).
  + simpl.
    Require HIT.epi.
    apply ap10.
    pose (epi.issurj_isepi eta _) as i.
    refine (i _ _ idmap _).
    apply path_forall.
    intro x.
    apply ap.
    symmetry.
    apply ah.
  + change (a o eta == idmap); symmetry.
    apply ah.
Defined.
