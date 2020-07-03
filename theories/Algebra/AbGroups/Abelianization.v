Require Import Basics Types Cubical WildCat.
Require Import Truncations.
Require Import HIT.Coeq.
Require Import Algebra.Groups.
Require Import Algebra.AbGroups.AbelianGroup.

(** In this file we define what it means for a group homomorphism G -> H into an abelian group H to be an abelianization. We then construct an example of an abelianization. *)

Local Open Scope mc_mult_scope.

(** Definition of Abelianization.

  A "unit" homomorphism [eta : G -> G_ab], with [G_ab] abelian, is considered an abelianization if and only if for all homomorphisms [G -> A], where [A] is abelian, there exists a unique [g : G_ab -> A] such that [h == g o eta X].   We express this in funext-free form by saying that precomposition with [eta] in the wild 1-category [Group] induces an equivalence of hom 0-groupoids.

  Unfortunately, if [eta : GroupHomomorphism G G_ab] and we write [cat_precomp A eta] then Coq is unable to guess that the relevant 1-category is [Group].  Even writing [cat_precomp (A := Group) A eta] isn't good enough, I guess because the typeclass inference that finds the instance [is01cat_group] doesn't happen until after the type of [eta] would have to be resolved to a [Hom] in some wild category.  However, with the following auxiliary definition we can force the typeclass inference to happen first.  (It would be worth thinking about whether the design of the wild categories library could be improved to avoid this.)  *)
Definition group_precomp {a b} := @cat_precomp Group _ _ a b.

Class IsAbelianization {G : Group} (G_ab : AbGroup)
      (eta : GroupHomomorphism G G_ab)
  := isequiv0gpd_isabel : forall (A : AbGroup),
      IsEquiv0Gpd (group_precomp A eta).
Global Existing Instance isequiv0gpd_isabel.

(** Here we define abelianization as a HIT. Specifically as a set-coequalizer of the following two maps: (a, b, c) |-> a (b c) and (a, b, c) |-> a (c b).

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
      (uncurry2 (fun a b c : G => a * (b * c)))
      (uncurry2 (fun a b c : G => a * (c * b)))).

  (** We have a natural map from G to Abel G. *)
  Definition ab : G -> Abel.
  Proof.
    intro g.
    apply tr, coeq, g.
  Defined.

  (** This map satisfies the condition ab_comm. *)
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
    srapply Trunc_ind.
    srapply Coeq_ind.
    1: apply a.
    intros [[x y] z].
    refine (transport_compose _ _ _ _ @ _).
    srapply dp_path_transport^-1%equiv.
    apply c.
  Defined.

  (** The computation rule can also be proven. *)
  Definition Abel_ind_beta_ab_comm (P : Abel -> Type)
    `{forall x, IsHSet (P x)}(a : forall x, P (ab x))
    (c : forall x y z, DPath P (ab_comm x y z)
      (a (x * (y * z))) (a (x * (z * y))))
    (x y z : G) : dp_apD (Abel_ind P a c) (ab_comm x y z) = c x y z.
  Proof.
    apply dp_apD_path_transport.
    refine (apD_compose' tr _ _ @ _).
    refine (ap _ (Coeq_ind_beta_cglue _ _ _ (x, y, z)) @ _).
    apply concat_V_pp.
  Defined.

  (** We also have a recursion princple. *)
  Definition Abel_rec (P : Type) `{IsHSet P} (a : G -> P)
    (c : forall x y z, a (x * (y * z)) = a (x * (z * y)))
    : Abel -> P.
  Proof.
    apply (Abel_ind _ a).
    intros; apply dp_const, c.
  Defined.

  (** Here is a simpler version of Abel_ind when our target is an HProp. This lets us discard all the higher paths. *)
  Definition Abel_ind_hprop (P : Abel -> Type) `{forall x, IsHProp (P x)} 
    (a : forall x, P (ab x)) : forall (x : Abel), P x.
  Proof.
    srapply (Abel_ind _ a).
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

(** The [IsHProp] argument of [Abel_ind_hprop] can usually be found by typeclass resolution, but [srapply] is slow, so we use this tactic instead. *)
Local Ltac Abel_ind_hprop x := snrapply Abel_ind_hprop; [exact _ | intro x].

(** We make sure that G is implicit in the arguments of ab and ab_comm. *)
Arguments ab {_}.
Arguments ab_comm {_}.

(** Now we can show that Abel G is in fact an abelian group. *)

Section AbelGroup.

  Context (G : Group).

  (** Firstly we derive the operation on Abel G. This is defined as follows:
        ab x + ab y := ab (x y)
      But we need to also check that it preserves ab_comm in the appropriate way. *)
  Global Instance abel_sgop : SgOp (Abel G).
  Proof.
    intro a.
    srapply Abel_rec.
    { intro b.
      revert a.
      srapply Abel_rec.
      { intro a.
        exact (ab (a * b)). }
      intros a c d; hnf.
      (* The pattern seems to be to alternate associativity and ab_comm. *)
      refine (ap _ (associativity _ _ _)^ @ _).
      refine (ab_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _) @ _).
      refine (ab_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _)^ @ _).
      refine (ab_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _)). }
    intros b c d.
    revert a.
    Abel_ind_hprop a; cbn.
    refine (ap _ (associativity _ _ _) @ _).
    refine (ab_comm _ _ _ @ _).
    refine (ap _ (associativity _ _ _)^).
  Defined.

  (** We can now easily show that this operation is associative by associativity in G and the fact that being associative is a proposition. *)
  Global Instance abel_sgop_associative : Associative abel_sgop.
  Proof.
    intros x y.
    Abel_ind_hprop z; revert y.
    Abel_ind_hprop y; revert x.
    Abel_ind_hprop x; cbn.
    apply ap, associativity.
  Defined.

  (** From this we know that Abel G is a semigroup. *)
  Global Instance abel_issemigroup : IsSemiGroup (Abel G) := {}.

  (** We define the unit as ab of the unit of G *)
  Global Instance abel_mon_unit : MonUnit (Abel G) := ab mon_unit.

  (** By using Abel_ind_hprop we can prove the left and right identity laws. *)
  Global Instance abel_leftidentity : LeftIdentity abel_sgop abel_mon_unit.
  Proof.
    Abel_ind_hprop x.
    cbn; apply ap, left_identity.
  Defined.

  Global Instance abel_rightidentity : RightIdentity abel_sgop abel_mon_unit.
  Proof.
    Abel_ind_hprop x.
    cbn; apply ap, right_identity.
  Defined.

  (** Hence Abel G is a monoid *)
  Global Instance ismonoid_abel : IsMonoid (Abel G) := {}.

  (** We can also prove that the operation is commutative! This will come in handy later. *)
  Global Instance abel_commutative : Commutative abel_sgop.
  Proof.
    intro x.
    Abel_ind_hprop y.
    revert x.
    Abel_ind_hprop x.
    cbn.
    refine ((ap ab (left_identity _))^ @ _).
    refine (_ @ (ap ab (left_identity _))).
    apply ab_comm.
  Defined.

  (** Now we can define the negation. This is just
        - (ab g) := (ab (g^-1))
      However when checking that it respects ab_comm we have to show the following:
        ab (- z * - y * - x) = ab (- y * - z * - x)
      there is no obvious way to do this, but we note that ab (x * y) is exactly the definition of ab x + ab y! Hence by commutativity we can show this. *)
  Global Instance abel_negate : Negate (Abel G).
  Proof.
    srapply Abel_rec.
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
    Abel_ind_hprop x.
    cbn; apply ap; apply left_inverse.
  Defined.

  Instance abel_rightinverse : RightInverse abel_sgop abel_negate abel_mon_unit.
  Proof.
    Abel_ind_hprop x.
    cbn; apply ap; apply right_inverse.
  Defined.

  (** Thus Abel G is a group *)
  Global Instance isgroup_abel : IsGroup (Abel G) := {}.

  (** And since the operation is commutative, an abelian group. *)
  Global Instance isabgroup_abel : IsAbGroup (Abel G) := {}.

  (** By definition, the map ab is also a group homomorphism. *)
  Global Instance issemigrouppreserving_ab : IsSemiGroupPreserving ab.
  Proof.
    by unfold IsSemiGroupPreserving.
  Defined.

End AbelGroup.

(** We can easily prove that ab is a surjection. *)
Global Instance issurj_ab {G : Group} : IsSurjection (@ab G).
Proof.
  apply BuildIsSurjection.
  Abel_ind_hprop x.
  cbn.
  apply tr.
  exists x.
  reflexivity.
Defined.

(** Now we finally check that our definition of abelianization satisfies the universal property of being an abelianization. *)

(** We define abel to be the abelianization of a group. This is a map from Group to AbGroup. *)
Definition abel : Group -> AbGroup.
Proof.
  intro G.
  srapply (Build_AbGroup (Abel G)).
Defined.

(** The unit of this map is the map ab which typeclasses can pick up to be a homomorphism. We write it out explicitly here. *)
Definition abel_unit (X : Group)
  : GroupHomomorphism X (abel X).
Proof.
  snrapply @Build_GroupHomomorphism.
  + exact ab.
  + exact _.
Defined.

(** Finally we can prove that our construction abel is an abelianization. *)
Global Instance isabelianization_abel {G : Group}
  : IsAbelianization (abel G) (abel_unit G).
Proof.
  intros A. constructor.
  { intros h. srefine (_;_).
    { snrapply @Build_GroupHomomorphism.
      { srapply (Abel_rec _ _ h).
        intros x y z.
        refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
        apply (ap (_ *.)).
        refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
        apply commutativity. }
      intros y.
      Abel_ind_hprop x; revert y.
      Abel_ind_hprop y.
      apply grp_homo_op. }
    cbn. reflexivity. }
  intros g h p.
  Abel_ind_hprop x.
  exact (p x).
Defined.

Theorem groupiso_isabelianization {G : Group}
  (A B : AbGroup)
  (eta1 : GroupHomomorphism G A)
  (eta2 : GroupHomomorphism G B)
  {isab1 : IsAbelianization A eta1}
  {isab2 : IsAbelianization B eta2}
  : GroupIsomorphism A B.
Proof.
  destruct (esssurj (group_precomp B eta1) eta2) as [a ac].
  destruct (esssurj (group_precomp A eta2) eta1) as [b bc].
  srapply (Build_GroupIsomorphism _ _ a).
  srapply (isequiv_adjointify _ b).
  { refine (essinj0 (group_precomp B eta2)
                    (x := a $o b) (y := Id (A := Group) B) _).
    intros x; cbn in *.
    refine (_ @ ac x).
    apply ap, bc. }
  { refine (essinj0 (group_precomp A eta1)
                    (x := b $o a) (y := Id (A := Group) A) _).
    intros x; cbn in *.
    refine (_ @ bc x).
    apply ap, ac. }
Defined.

Theorem homotopic_isabelianization {G : Group} (A B : AbGroup)
  (eta1 : GroupHomomorphism G A) (eta2 : GroupHomomorphism G B)
  {isab1 : IsAbelianization A eta1} {isab2 : IsAbelianization B eta2}
  : eta2 == grp_homo_compose (groupiso_isabelianization A B eta1 eta2) eta1.
Proof.
  intros x.
  exact (((esssurj (group_precomp B eta1) eta2).2 x)^).
Defined.

(** Hence any abelianization is surjective. *)
Global Instance issurj_isabelianization {G : Group}
  (A : AbGroup) (eta : GroupHomomorphism G A)
  : IsAbelianization A eta -> IsSurjection eta.
Proof.
  intros k.
  pose (homotopic_isabelianization A (abel G) eta (abel_unit G)) as p.
  refine (@cancelR_isequiv_conn_map _ _ _ _ _ _ _
    (conn_map_homotopic _ _ _ p _)).
Defined.

Global Instance isabelianization_identity (A : AbGroup) : IsAbelianization A grp_homo_id.
Proof.
  intros B. constructor.
  - intros h; exact (h ; fun _ => idpath).
  - intros g h p; exact p.
Defined.

Global Instance isequiv_abgroup_abelianization
  (A B : AbGroup) (eta : GroupHomomorphism A B) {isab : IsAbelianization B eta}
  : IsEquiv eta.
Proof.
  srapply isequiv_homotopic.
  - srapply (groupiso_isabelianization A B grp_homo_id eta).
  - exact _.
  - symmetry; apply homotopic_isabelianization.
Defined.
