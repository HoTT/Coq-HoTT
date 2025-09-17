From HoTT Require Import Basics Types Truncations.Core.
Require Import Cubical.DPath WildCat.
Require Import Colimits.Coeq.
Require Import Algebra.AbGroups.AbelianGroup.
Require Import Modalities.ReflectiveSubuniverse.

(** * Abelianization *)

(** In this file we define what it means for a group homomorphism [G -> H] into an abelian group [H] to be an abelianization. We then construct an example of an abelianization. *)

Local Open Scope mc_scope.
Local Open Scope mc_mult_scope.
Local Open Scope wc_iso_scope.

(** ** Definition of abelianization.

  A "unit" homomorphism [eta : G -> G_ab], with [G_ab] abelian, is considered an abelianization if and only if for all homomorphisms [G -> A], where [A] is abelian, there exists a unique [g : G_ab -> A] such that [h == g o eta X].   We express this in funext-free form by saying that precomposition with [eta] in the wild 1-category [Group] induces an equivalence of hom 0-groupoids, in the sense of WildCat/EquivGpd.

  Unfortunately, if [eta : GroupHomomorphism G G_ab] and we write [cat_precomp A eta] then Coq is unable to guess that the relevant 1-category is [Group].  Even writing [cat_precomp (A := Group) A eta] isn't good enough, I guess because the typeclass inference that finds the instance [is01cat_group] doesn't happen until after the type of [eta] would have to be resolved to a [Hom] in some wild category.  However, with the following auxiliary definition we can force the typeclass inference to happen first.  (It would be worth thinking about whether the design of the wild categories library could be improved to avoid this.)  *)
Definition group_precomp {a b} := @cat_precomp Group _ _ a b.

Class IsAbelianization {G : Group} (G_ab : AbGroup)
      (eta : GroupHomomorphism G G_ab)
  := issurjinj_isabel :: forall (A : AbGroup),
      IsSurjInj (group_precomp A eta).

Definition isequiv_group_precomp_isabelianization `{Funext}
  {G : Group} {G_ab : AbGroup} (eta : GroupHomomorphism G G_ab)
  `{!IsAbelianization G_ab eta} (A : AbGroup)
  : IsEquiv (group_precomp A eta).
Proof.
  snapply isequiv_adjointify.
  - intros g.
    exact (surjinj_inv (group_precomp A eta) g).
  - intros f.
    snapply equiv_path_grouphomomorphism.
    exact (eisretr0gpd_inv (group_precomp A eta) f).
  - intros f.
    snapply equiv_path_grouphomomorphism.
    exact (eissect0gpd_inv (group_precomp A eta) f).
Defined.

Definition equiv_group_precomp_isabelianization `{Funext}
  {G : Group} {G_ab : AbGroup} (eta : GroupHomomorphism G G_ab)
  `{!IsAbelianization G_ab eta} (A : AbGroup)
  : (G_ab $-> A) <~> (G $-> A)
  := Build_Equiv _ _ _ (isequiv_group_precomp_isabelianization eta A).

(** Here we define abelianization as a HIT. Specifically as a set-coequalizer of the following two maps [fun '(a, b, c) => a * (b * c)] and [fun '(a, b, c) => a * (c * b)].

From this we can show that Abel G is an abelian group.

In fact this models the following HIT:

<<
HIT Abel (G : Group) := 
 | abel_in : G -> Abel G
 | abel_in_comm : forall x y z, abel_in (x * (y * z)) = abel_in (x * (z * y)).
>>

We also derive [abel_in] and [abel_in_comm] from our coequalizer definition, and even prove the induction and computation rules for this HIT.

This HIT was suggested by Dan Christensen. *)

Section Abel.

  (** Let G be a group. *)
  Context (G : Group).

  (** We locally define a map uncurry2 that lets us uncurry [A * B * C -> D] twice. *)
  Local Definition uncurry2 {A B C D : Type}
    : (A -> B -> C -> D) -> A * B * C -> D
    := fun f '(a, b, c) => f a b c.

  (** The type [Abel] is defined to be the set coequalizer of the following maps [G^3 -> G]. *)
  Definition Abel
    := Tr 0 (Coeq
      (uncurry2 (fun a b c : G => a * (b * c)))
      (uncurry2 (fun a b c : G => a * (c * b)))).

  (** We have a natural map from [G] to [Abel G]. *)
  Definition abel_in : G -> Abel := tr o coeq.

  (** This map satisfies the condition [ab_comm]. It's a form of commutativity in a right factor. *)
  Definition abel_in_comm a b c
    : abel_in (a * (b * c)) = abel_in (a * (c * b))
    := ap tr (cglue (a, b, c)).

  (** It is clear that Abel is a set. *)
  Definition istrunc_abel : IsHSet Abel := _.

  (** We can derive the induction principle from the ones for truncation and the coequalizer. *)
  Definition Abel_ind (P : Abel -> Type) `{forall x, IsHSet (P x)} 
    (a : forall x, P (abel_in x))
    (c : forall x y z, abel_in_comm x y z # a (x * (y * z)) = a (x * (z * y)))
    : forall (x : Abel), P x.
  Proof.
    rapply Trunc_ind.
    snapply Coeq_ind.
    1: exact a.
    intros [[x y] z].
    nrefine (transport_compose _ _ _ _ @ _).
    apply c.
  Defined.

  (** The computation rule on point constructors holds definitionally. *)
  Definition Abel_ind_beta_abel_in (P : Abel -> Type) `{forall x, IsHSet (P x)}
    (a : forall x, P (abel_in x))
    (c : forall x y z, DPath P (abel_in_comm x y z) (a (x * (y * z))) (a (x * (z * y))))
    (x : G)
    : Abel_ind P a c (abel_in x) = a x
    := idpath.

  (** The computation rule on paths. *)
  Definition Abel_ind_beta_abel_in_comm (P : Abel -> Type) `{forall x, IsHSet (P x)}
    (a : forall x, P (abel_in x))
    (c : forall x y z, abel_in_comm x y z # a (x * (y * z)) = a (x * (z * y)))
    (x y z : G)
    : apD (Abel_ind P a c) (abel_in_comm x y z) = c x y z.
  Proof.
    nrefine (apD_compose' tr _ _ @ ap _ _ @ concat_V_pp _ _).
    rapply Coeq_ind_beta_cglue.
  Defined.

  (** We also have a recursion principle. *)
  Definition Abel_rec (P : Type) `{IsHSet P} (a : G -> P)
    (c : forall x y z, a (x * (y * z)) = a (x * (z * y)))
    : Abel -> P.
  Proof.
    apply (Abel_ind _ a).
    intros; apply dp_const, c.
  Defined.

  (** Here is a simpler version of [Abel_ind] when our target is an [HProp]. This lets us discard all the higher paths. *)
  Definition Abel_ind_hprop (P : Abel -> Type) `{forall x, IsHProp (P x)} 
    (a : forall x, P (abel_in x))
    : forall (x : Abel), P x.
  Proof.
    srapply Trunc_ind.
    srapply Coeq_ind_hprop.
    exact a.
  Defined.

End Abel.

(** The [IsHProp] argument of [Abel_ind_hprop] can usually be found by typeclass resolution, but [srapply] is slow, so we use this tactic instead. *)
Local Ltac Abel_ind_hprop x := snapply Abel_ind_hprop; [exact _ | intro x].

(** We make sure that [G] is implicit in the arguments of [abel_in]
 and [abel_in_comm]. *)
Arguments abel_in {_} g%_mc_mult_scope.
Arguments abel_in_comm {_} (a b c)%_mc_mult_scope.

(** Now we can show that [Abel G] is in fact an abelian group. We will denote the operation in [Abel G] by the multiplicative [*] notation even though it is later shown to be commutative. *)

Section AbelGroup.

  Context (G : Group).

  (** Firstly we define the operation on [Abel G]. This is defined as follows:
<<
        abel_in x * abel_in y := abel_in (x * y)
>>
      But we need to also check that it preserves [ab_comm] in the appropriate way. *)
  #[export] Instance sgop_abel : SgOp (Abel G).
  Proof.
    intro a.
    srapply Abel_rec.
    { intro b.
      revert a.
      srapply Abel_rec.
      { intro a.
        exact (abel_in (a * b)). }
      intros a c d; hnf.
      (* The pattern seems to be to alternate [associativity] and [ab_comm]. *)
      refine (ap _ (associativity _ _ _)^ @ _).
      refine (abel_in_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _) @ _).
      refine (abel_in_comm _ _ _ @ _).
      refine (ap _ (associativity _ _ _)^ @ _).
      refine (abel_in_comm _ _ _ @ _).
      exact (ap _ (associativity _ _ _)). }
    intros b c d.
    revert a.
    Abel_ind_hprop a; simpl.
    refine (ap _ (associativity _ _ _) @ _).
    refine (abel_in_comm _ _ _ @ _).
    exact (ap _ (associativity _ _ _)^).
  Defined.

  (** We can now easily show that this operation is associative by [associativity] in [G] and the fact that being associative is a proposition. *)
  #[export] Instance associative_abel_sgop : Associative (.*.).
  Proof.
    intros x y.
    Abel_ind_hprop z; revert y.
    Abel_ind_hprop y; revert x.
    Abel_ind_hprop x; simpl.
    napply (ap abel_in); apply associativity.
  Defined.

  (** From this we know that [Abel G] is a semigroup. *)
  #[export] Instance issemigroup_abel : IsSemiGroup (Abel G) := {}.

  (** We define the group unit as [abel_in] of the unit of [G] *)
  #[export] Instance monunit_abel_zero : MonUnit (Abel G) := abel_in mon_unit.

  (** By using Abel_ind_hprop we can prove the left and right identity laws. *)
  #[export] Instance leftidentity_abel : LeftIdentity (.*.) 1.
  Proof.
    Abel_ind_hprop x; cbn beta.
    napply (ap abel_in); apply left_identity.
  Defined.

  #[export] Instance rightidentity_abel : RightIdentity (.*.) 1.
  Proof.
    Abel_ind_hprop x; cbn beta.
    napply (ap abel_in); apply right_identity.
  Defined.

  (** Hence [Abel G] is a monoid *)
  #[export] Instance ismonoid_abel : IsMonoid (Abel G) := {}.

  (** We can also prove that the operation is commutative! This will come in handy later. *)
  #[export] Instance commutative_abel : Commutative (.*.).
  Proof.
    intro x.
    Abel_ind_hprop y.
    revert x.
    Abel_ind_hprop x; cbn beta.
    refine ((ap abel_in (left_identity _))^ @ _).
    refine (_ @ (ap abel_in (left_identity _))).
    apply abel_in_comm.
  Defined.

  (** Now we can define the inverse operation. This is just
<<
        (abel_in g)^ := abel_in g^
>>
      However when checking that it respects [ab_comm] we have to show the following:
<<
        abel_in (z^ * y^ * x^) = abel_in (y^ * z^ * x^)
>>
      there is no obvious way to do this, but we note that [abel_in (x * y)] is exactly the definition of [abel_in x * abel_in y]! Hence by [commutativity] we can show this. *)
  #[export] Instance inverse_abel : Inverse (Abel G).
  Proof.
    srapply (Abel_rec _ _ (abel_in o inv)).
    intros x y z; cbn beta.
    lhs napply ap.
    2: rhs napply ap.
    1,3: lhs rapply inverse_sg_op; napply (ap (.* _)); rapply inverse_sg_op.
    change (abel_in z^ * abel_in y^ * abel_in x^
      = abel_in y^ * abel_in z^ * abel_in x^).
    apply (ap (.* _)).
    exact (commutativity (abel_in z^) (abel_in y^)).
  Defined.

  (** Again by [Abel_ind_hprop] and the corresponding laws for [G] we can prove the left and right inverse laws. *)
  #[export] Instance leftinverse_abel : LeftInverse (.*.) (^) 1.
  Proof.
    Abel_ind_hprop x; simpl.
    napply (ap abel_in); apply left_inverse.
  Defined.

  Instance rightinverse_abel : RightInverse (.*.) (^) 1.
  Proof.
    Abel_ind_hprop x; simpl.
    napply (ap abel_in); apply right_inverse.
  Defined.

  (** Thus [Abel G] is a group *)
  #[export] Instance isgroup_abel : IsGroup (Abel G) := {}.

  (** And furthermore, since the operation is commutative, it is an abelian group. *)
  #[export] Instance isabgroup_abel : IsAbGroup (Abel G) := {}.

  (** By definition, the map [abel_in] is also a group homomorphism. *)
  #[export] Instance issemigrouppreserving_abel_in : IsSemiGroupPreserving abel_in.
  Proof.
    by unfold IsSemiGroupPreserving.
  Defined.

End AbelGroup.

(** We can easily prove that [abel_in] is a surjection. *)
Instance issurj_abel_in {G : Group} : IsSurjection (@abel_in G).
Proof.
  apply BuildIsSurjection.
  Abel_ind_hprop x; cbn beta.
  apply tr.
  exists x.
  reflexivity.
Defined.

(** Now we finally check that our definition of abelianization satisfies the universal property of being an abelianization. *)

(** We define [abel] to be the abelianization of a group. This is a map from [Group] to [AbGroup]. *)
Definition abel : Group -> AbGroup.
Proof.
  intro G.
  snapply Build_AbGroup.
  - srapply (Build_Group (Abel G)).
  - exact _.
Defined.

(** We don't wish for [abel G] to be unfolded when using [simpl] or [cbn]. *)
Arguments abel G : simpl never.

(** The unit of this map is the map [abel_in] which typeclasses can pick up to be a homomorphism. We write it out explicitly here. *)
Definition abel_unit {G : Group} : G $-> abel G
  := @Build_GroupHomomorphism G (abel G) abel_in _.

Definition grp_homo_abel_rec {G : Group} {A : AbGroup} (f : G $-> A)
  : abel G $-> A.
Proof.
  snapply Build_GroupHomomorphism.
  { srapply (Abel_rec _ _ f).
    intros x y z.
    napply grp_homo_op_agree; trivial.
    refine (grp_homo_op _ _ _ @ _ @ (grp_homo_op _ _ _)^).
    apply commutativity. }
  intros y.
  Abel_ind_hprop x; revert y.
  Abel_ind_hprop y.
  apply grp_homo_op.
Defined.

Definition abel_ind_homotopy {G H : Group} {f g : Hom (A:=Group) (abel G) H}
  (p : f $o abel_unit $== g $o abel_unit)
  : f $== g.
Proof.
  rapply Abel_ind_hprop.
  exact p.
Defined.

(** Finally we can prove that our construction abel is an abelianization. *)
Instance isabelianization_abel {G : Group}
  : IsAbelianization (abel G) abel_unit.
Proof.
  intros A. constructor.
  { intros h.
    snrefine (grp_homo_abel_rec h; _).
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
  : A ≅ B.
Proof.
  destruct (esssurj (group_precomp B eta1) eta2) as [a ac].
  destruct (esssurj (group_precomp A eta2) eta1) as [b bc].
  srapply (Build_GroupIsomorphism _ _ a).
  srapply (isequiv_adjointify _ b).
  { refine (essinj (group_precomp B eta2)
                   (x := a $o b) (y := Id (A := Group) B) _).
    intros x; cbn in *.
    refine (_ @ ac x).
    apply ap, bc. }
  { refine (essinj (group_precomp A eta1)
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
  symmetry.
  exact ((esssurj (group_precomp B eta1) eta2).2 x).
Defined.

(** Hence any abelianization is surjective. *)
Instance issurj_isabelianization {G : Group}
  (A : AbGroup) (eta : GroupHomomorphism G A)
  : IsAbelianization A eta -> IsSurjection eta.
Proof.
  intros k.
  pose (homotopic_isabelianization A (abel G) eta abel_unit) as p.
  exact (@cancelL_isequiv_conn_map _ _ _ _ _ _ _
    (conn_map_homotopic _ _ _ p _)).
Defined.

Instance isabelianization_identity (A : AbGroup) : IsAbelianization A grp_homo_id.
Proof.
  intros B. constructor.
  - intros h; exact (h ; fun _ => idpath).
  - intros g h p; exact p.
Defined.

Instance isequiv_abgroup_abelianization
  (A B : AbGroup) (eta : GroupHomomorphism A B) {isab : IsAbelianization B eta}
  : IsEquiv eta.
Proof.
  srapply isequiv_homotopic.
  - exact (groupiso_isabelianization A B grp_homo_id eta).
  - exact _.
  - symmetry; apply homotopic_isabelianization.
Defined.

(** ** Functoriality *)

Instance is0functor_abel : Is0Functor abel.
Proof.
  snapply Build_Is0Functor.
  intros A B f.
  snapply grp_homo_abel_rec.
  exact (abel_unit $o f).
Defined.

Instance is1functor_abel : Is1Functor abel.
Proof.
  snapply Build_Is1Functor.
  - intros A B f g p.
    unfold abel.
    rapply Abel_ind_hprop.
    intros x.
    exact (ap abel_in (p x)).
  - intros A.
    by rapply Abel_ind_hprop.
  - intros A B C f g.
    by rapply Abel_ind_hprop.
Defined.
