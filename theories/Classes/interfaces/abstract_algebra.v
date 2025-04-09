Require Export Basics.Classes Basics.Overture.
Require Import Spaces.Nat.Core.
Require Export HoTT.Classes.interfaces.canonical_names.
Require Import Modalities.ReflectiveSubuniverse.

Local Set Polymorphic Inductive Cumulativity.

Generalizable Variables A B C f g x y.

(*
For various structures we omit declaration of substructures. For example, if we
say:

Class Setoid_Morphism :=
  { setoidmor_a : Setoid A
  ; setoidmor_b : Setoid B
  ; sm_proper : Proper ((=) ==> (=)) f }.
#[export] Existing Instances setoidmor_a setoidmor_b sm_proper.

then each time a Setoid instance is required, Coq will try to prove that a
Setoid_Morphism exists. This obviously results in an enormous blow-up of the
search space. Moreover, one should be careful to declare a Setoid_Morphisms
as a substructure. Consider [f t1 t2], now if we want to perform setoid rewriting
in [t2] Coq will first attempt to prove that [f t1] is Proper, for which it will
attempt to prove [Setoid_Morphism (f t1)]. If many structures declare
Setoid_Morphism as a substructure, setoid rewriting will become horribly slow.
*)

(* An unbundled variant of the former CoRN CSetoid. We do not
  include a proof that A is a Setoid because it can be derived. *)
Class IsApart A {Aap : Apart A} : Type :=
  { apart_set :: IsHSet A
  ; apart_mere :: is_mere_relation _ apart
  ; apart_symmetric :: Symmetric (≶)
  ; apart_cotrans :: CoTransitive (≶)
  ; tight_apart : forall x y, ~(x ≶ y) <-> x = y }.

Instance apart_irrefl `{IsApart A} : Irreflexive (≶).
Proof.
intros x ap.
apply (tight_apart x x).
- reflexivity.
- assumption.
Qed.

Arguments tight_apart {A Aap IsApart} _ _.

Section setoid_morphisms.
  Context {A B} {Aap : Apart A} {Bap : Apart B} (f : A -> B).

  Class StrongExtensionality := strong_extensionality : forall x y, f x ≶ f y -> x ≶ y.
End setoid_morphisms.

(* HOTT TODO check if this is ok/useful *)
#[export]
Hint Extern 4 (?f _ = ?f _) => eapply (ap f) : core.

Section setoid_binary_morphisms.
  Context {A B C} {Aap: Apart A}
    {Bap : Apart B} {Cap : Apart C} (f : A -> B -> C).

  Class StrongBinaryExtensionality := strong_binary_extensionality
    : forall x₁ y₁ x₂ y₂, f x₁ y₁ ≶ f x₂ y₂ -> hor (x₁ ≶ x₂) (y₁ ≶ y₂).
End setoid_binary_morphisms.

(*
Since apartness usually only becomes relevant when considering fields (e.g. the
real numbers), we do not include it in the lower part of the algebraic hierarchy
(as opposed to CoRN).
*)
Section upper_classes.
  Universe i.
  Context (A : Type@{i}).

  Local Open Scope mc_mult_scope.

  Class IsSemiGroup {Aop: SgOp A} :=
    { sg_set :: IsHSet A
    ; sg_ass :: Associative (.*.) }.

  Class IsCommutativeSemiGroup {Aop : SgOp A} :=
    { comsg_sg :: @IsSemiGroup (.*.)
    ; comsg_comm :: Commutative (.*.) }.

  Class IsSemiLattice {Aop : SgOp A} :=
    { semilattice_sg :: @IsCommutativeSemiGroup (.*.)
    ; semilattice_idempotent :: BinaryIdempotent (.*.)}.

  Class IsMonoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { monoid_semigroup :: IsSemiGroup
    ; monoid_left_id :: LeftIdentity (.*.) mon_unit
    ; monoid_right_id :: RightIdentity (.*.) mon_unit }.

  Class IsCommutativeMonoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { commonoid_mon :: @IsMonoid (.*.) Aunit
    ; commonoid_commutative :: Commutative (.*.) }.

  Class IsGroup {Aop : SgOp A} {Aunit : MonUnit A} {Ainv : Inverse A} :=
    { group_monoid :: @IsMonoid (.*.) mon_unit
    ; inverse_l :: LeftInverse (.*.) (^) mon_unit
    ; inverse_r :: RightInverse (.*.) (^) mon_unit
    }.

  Class IsBoundedSemiLattice {Aop : SgOp A} {Aunit : MonUnit A} :=
    { bounded_semilattice_mon :: @IsCommutativeMonoid (.*.) Aunit
    ; bounded_semilattice_idempotent :: BinaryIdempotent (.*.)}.
  
  Local Close Scope mc_mult_scope.

  Class IsAbGroup {Aop : SgOp A} {Aunit : MonUnit A} {Ainv : Inverse A} :=
    { abgroup_group :: @IsGroup Aop Aunit Ainv
    ; abgroup_commutative :: Commutative Aop }.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class IsSemiCRing :=
    { semiplus_monoid :: @IsCommutativeMonoid (+) 0
    ; semimult_monoid :: @IsCommutativeMonoid (.*.) 1
    ; semiring_distr :: LeftDistribute (.*.) (+)
    ; semiring_left_absorb :: LeftAbsorb (.*.) 0 }.

  Context {Anegate : Negate A}.

  Class IsRing :=
    { ring_abgroup :: @IsAbGroup (+) 0 (-)
    ; ring_monoid :: @IsMonoid (.*.) 1
    ; ring_dist_left :: LeftDistribute (.*.) (+)
    ; ring_dist_right :: RightDistribute (.*.) (+)
  }.

  Class IsCRing :=
    { cring_group :: @IsAbGroup (+) 0 (-)
    ; cring_monoid :: @IsCommutativeMonoid (.*.) 1
    ; cring_dist :: LeftDistribute (.*.) (+) }.

  #[export] Instance isring_iscring : IsCRing -> IsRing.
  Proof.
    intros H.
    econstructor; try exact _.
    intros a b c.
    lhs rapply commutativity.
    lhs rapply distribute_l.
    f_ap; apply commutativity.
  Defined.

  Class IsIntegralDomain :=
    { intdom_ring : IsCRing
    ; intdom_nontrivial : PropHolds (not (1 = 0))
    ; intdom_nozeroes :: NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/)
    because it can be derived *)
  Class IsField {Aap: Apart A} {Arecip: Recip A} :=
    { field_ring :: IsCRing
    ; field_apart :: IsApart A
    ; field_plus_ext :: StrongBinaryExtensionality (+)
    ; field_mult_ext :: StrongBinaryExtensionality (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_inverse : forall x, x.1 // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/),
    f (/x) = / (f x), / /x = x, /x * /y = /(x * y)
    hold without any additional assumptions *)
  Class IsDecField {Adec_recip : DecRecip A} :=
    { decfield_ring :: IsCRing
    ; decfield_nontrivial : PropHolds (1 <> 0)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : forall x, x <> 0 -> x / x = 1 }.

  Class FieldCharacteristic@{j} {Aap : Apart@{i j} A} (k : nat) : Type@{j}
    := field_characteristic : forall n : nat,
        Nat.Core.lt 0 n ->
        iff@{j j j} (forall m : nat, not@{j} (paths@{Set} n
                                                  (nat_mul k m)))
        (@apart A Aap (nat_iter n (1 +) 0) 0).

End upper_classes.

(* Due to bug #2528 *)
#[export]
Hint Extern 4 (PropHolds (1 <> 0)) =>
  eapply @intdom_nontrivial : typeclass_instances.
#[export]
Hint Extern 5 (PropHolds (1 ≶ 0)) =>
  eapply @field_nontrivial : typeclass_instances.
#[export]
Hint Extern 5 (PropHolds (1 <> 0)) =>
  eapply @decfield_nontrivial : typeclass_instances.

(*
For a strange reason IsCRing instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> IsCRing forces Coq to
take the right way
*)
#[export]
Hint Extern 10 (IsCRing _) => apply @intdom_ring : typeclass_instances.

Arguments recip_inverse {A Aplus Amult Azero Aone Anegate Aap Arecip IsField} _.
Arguments dec_recip_inverse
  {A Aplus Amult Azero Aone Anegate Adec_recip IsDecField} _ _.
Arguments dec_recip_0 {A Aplus Amult Azero Aone Anegate Adec_recip IsDecField}.

Section lattice.
  Context A {Ajoin: Join A} {Ameet: Meet A} {Abottom : Bottom A} {Atop : Top A}.

  Class IsJoinSemiLattice :=
    join_semilattice :: @IsSemiLattice A join_is_sg_op.

  Class IsBoundedJoinSemiLattice :=
    bounded_join_semilattice :: @IsBoundedSemiLattice A
      join_is_sg_op bottom_is_mon_unit.

  Class IsMeetSemiLattice :=
    meet_semilattice :: @IsSemiLattice A meet_is_sg_op.

  Class IsBoundedMeetSemiLattice :=
    bounded_meet_semilattice :: @IsBoundedSemiLattice A
      meet_is_sg_op top_is_mon_unit.

  Class IsLattice :=
    { lattice_join :: IsJoinSemiLattice
    ; lattice_meet :: IsMeetSemiLattice
    ; join_meet_absorption :: Absorption (⊔) (⊓)
    ; meet_join_absorption :: Absorption (⊓) (⊔) }.

  Class IsBoundedLattice :=
    { boundedlattice_join :: IsBoundedJoinSemiLattice
    ; boundedlattice_meet :: IsBoundedMeetSemiLattice
    ; boundedjoin_meet_absorption :: Absorption (⊔) (⊓)
    ; boundedmeet_join_absorption :: Absorption (⊓) (⊔)}.

  Class IsDistributiveLattice :=
    { distr_lattice_lattice :: IsLattice
    ; join_meet_distr_l :: LeftDistribute (⊔) (⊓) }.

End lattice.

Section morphism_classes.

  Section sgmorphism_classes.
  Context {A B : Type} {Aop : SgOp A} {Bop : SgOp B}
    {Aunit : MonUnit A} {Bunit : MonUnit B}.

  Local Open Scope mc_mult_scope.

  Class IsSemiGroupPreserving (f : A -> B) :=
    preserves_sg_op : forall x y, f (x * y) = f x * f y.

  Class IsUnitPreserving (f : A -> B) :=
    preserves_mon_unit : f mon_unit = mon_unit.

  Class IsMonoidPreserving (f : A -> B) :=
    { monmor_sgmor :: IsSemiGroupPreserving f
    ; monmor_unitmor :: IsUnitPreserving f }.

  End sgmorphism_classes.

  Section ringmorphism_classes.
  Context {A B : Type} {Aplus : Plus A} {Bplus : Plus B}
    {Amult : Mult A} {Bmult : Mult B} {Azero : Zero A} {Bzero : Zero B}
    {Aone : One A} {Bone : One B}.

  Class IsSemiRingPreserving (f : A -> B) :=
    { semiringmor_plus_mor :: @IsMonoidPreserving A B
        (+) (+) 0 0 f
    ; semiringmor_mult_mor :: @IsMonoidPreserving A B
        (.*.) (.*.) 1 1 f }.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class IsSemiRingStrongPreserving (f : A -> B) :=
    { strong_semiringmor_sr_mor :: IsSemiRingPreserving f
    ; strong_semiringmor_strong_mor :: StrongExtensionality f }.

  End ringmorphism_classes.

  Section latticemorphism_classes.
  Context {A B : Type} {Ajoin : Join A} {Bjoin : Join B}
    {Ameet : Meet A} {Bmeet : Meet B}.

  Class IsJoinPreserving (f : A -> B) :=
    join_slmor_sgmor :: @IsSemiGroupPreserving A B join_is_sg_op join_is_sg_op f.

  Class IsMeetPreserving (f : A -> B) :=
    meet_slmor_sgmor :: @IsSemiGroupPreserving A B meet_is_sg_op meet_is_sg_op f.

  Context {Abottom : Bottom A} {Bbottom : Bottom B}.
  Class IsBoundedJoinPreserving (f : A -> B) := bounded_join_slmor_monmor
      :: @IsMonoidPreserving A B join_is_sg_op join_is_sg_op
         bottom_is_mon_unit bottom_is_mon_unit f.

  Class IsLatticePreserving (f : A -> B) :=
    { latticemor_join_mor :: IsJoinPreserving f
    ; latticemor_meet_mor :: IsMeetPreserving f }.

  End latticemorphism_classes.
End morphism_classes.

Section id_mor.
  Context `{SgOp A} `{MonUnit A}.

  #[export] Instance id_sg_morphism : IsSemiGroupPreserving (@id A).
  Proof.
    split.
  Defined.

  #[export] Instance id_monoid_morphism : IsMonoidPreserving (@id A).
  Proof.
    split; split.
  Defined.
End id_mor.

Section compose_mor.

  Context
    `{SgOp A} `{MonUnit A}
    `{SgOp B} `{MonUnit B}
    `{SgOp C} `{MonUnit C}
    (f : A -> B) (g : B -> C).

  (** Making these global instances causes typeclass loops.  Instead they are declared below as [Hint Extern]s that apply only when the goal has the specified form. *)
  Local Instance compose_sg_morphism : IsSemiGroupPreserving f -> IsSemiGroupPreserving g ->
    IsSemiGroupPreserving (g ∘ f).
  Proof.
    red; intros fp gp x y.
    unfold Compose.
    refine ((ap g _) @ _).
    - apply fp.
    - apply gp.
  Defined.

  Local Instance compose_monoid_morphism : IsMonoidPreserving f -> IsMonoidPreserving g ->
    IsMonoidPreserving (g ∘ f).
  Proof.
    intros;split.
    - exact _.
    - red;unfold Compose.
      etransitivity;[|exact (preserves_mon_unit (f:=g))].
      apply ap,preserves_mon_unit.
  Defined.

End compose_mor.

Section invert_mor.

  Context
    `{SgOp A} `{MonUnit A}
    `{SgOp B} `{MonUnit B}
    (f : A -> B).

  Local Instance invert_sg_morphism
    : forall `{!IsEquiv f}, IsSemiGroupPreserving f ->
      IsSemiGroupPreserving (f^-1).
  Proof.
    red; intros E fp x y.
    apply (equiv_inj f).
    lhs napply eisretr.
    symmetry.
    lhs napply fp.
    f_ap; apply eisretr.
  Defined.

  Local Instance invert_monoid_morphism :
    forall `{!IsEquiv f}, IsMonoidPreserving f -> IsMonoidPreserving (f^-1).
  Proof.
    intros;split.
    - exact _.
    - apply (equiv_inj f).
      refine (_ @ _).
      + apply eisretr.
      + symmetry; exact preserves_mon_unit.
  Defined.

End invert_mor.

#[export]
Hint Extern 4 (IsSemiGroupPreserving (_ ∘ _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.
#[export]
Hint Extern 4 (IsMonoidPreserving (_ ∘ _)) =>
  class_apply @compose_monoid_morphism : typeclass_instances.

#[export]
Hint Extern 4 (IsSemiGroupPreserving (_ o _)) =>
  class_apply @compose_sg_morphism : typeclass_instances.
#[export]
Hint Extern 4 (IsMonoidPreserving (_ o _)) =>
  class_apply @compose_monoid_morphism : typeclass_instances.

#[export]
Hint Extern 4 (IsSemiGroupPreserving (_^-1)) =>
  class_apply @invert_sg_morphism : typeclass_instances.
#[export]
Hint Extern 4 (IsMonoidPreserving (_^-1)) =>
  class_apply @invert_monoid_morphism : typeclass_instances.

#[export]
Instance isinjective_mapinO_tr {A B : Type} (f : A -> B)
  {p : MapIn (Tr (-1)) f} : IsInjective f
  := fun x y pfeq => ap pr1 (@center _ (p (f y) (x; pfeq) (y; idpath))).

Section strong_injective.
  Context {A B} {Aap : Apart A} {Bap : Apart B} (f : A -> B) .
  Class IsStrongInjective :=
    { strong_injective : forall x y, x ≶ y -> f x ≶ f y
    ; strong_injective_mor : StrongExtensionality f }.
End strong_injective.

Section extras.

Class CutMinusSpec A (cm : CutMinus A) `{Zero A} `{Plus A} `{Le A} := {
  cut_minus_le : forall x y, y ≤ x -> x ∸ y + y = x ;
  cut_minus_0 : forall x y, x ≤ y -> x ∸ y = 0
}.

#[export] Instance istrunc_isunitpreserving `{Funext} {n A B} unitA unitB f
  : IsTrunc n.+1 B -> IsTrunc n (@IsUnitPreserving A B unitA unitB f).
Proof.
  unfold IsUnitPreserving; exact _.
Defined.

#[export] Instance istrunc_issemigrouppreserving `{Funext} {n A B} opA opB f
  : IsTrunc n.+1 B -> IsTrunc n (@IsSemiGroupPreserving A B opA opB f).
Proof.
  unfold IsSemiGroupPreserving; exact _.
Defined.

Definition issig_IsSemiRingPreserving {A B : Type}
  `{Plus A, Plus B, Mult A, Mult B, Zero A, Zero B, One A, One B} {f : A -> B}
  : _ <~> IsSemiRingPreserving f := ltac:(issig).

Definition issig_IsMonoidPreserving {A B : Type} `{SgOp A} `{SgOp B}
  `{MonUnit A} `{MonUnit B} {f : A -> B} : _ <~> IsMonoidPreserving f
  := ltac:(issig).

#[export] Instance ishprop_ismonoidpreserving `{Funext} {A B : Type} `{SgOp A}
  `{SgOp B} `{IsHSet B} `{MonUnit A} `{MonUnit B} (f : A -> B)
  : IsHProp (IsMonoidPreserving f)
  := istrunc_equiv_istrunc _ issig_IsMonoidPreserving.

#[export] Instance ishprop_issemiringpreserving `{Funext} {A B : Type} `{IsHSet B}
  `{Plus A, Plus B, Mult A, Mult B, Zero A, Zero B, One A, One B}
  (f : A -> B)
  : IsHProp (IsSemiRingPreserving f)
  := istrunc_equiv_istrunc _ issig_IsSemiRingPreserving.

Definition issig_issemigroup x y : _ <~> @IsSemiGroup x y := ltac:(issig).

#[export] Instance ishprop_issemigroup `{Funext} x y
  : IsHProp (@IsSemiGroup x y)
  := istrunc_equiv_istrunc _ (issig_issemigroup _ _).

Definition issig_ismonoid x y z : _ <~> @IsMonoid x y z := ltac:(issig).

#[export] Instance ishprop_ismonoid `{Funext} x y z : IsHProp (@IsMonoid x y z)
  := istrunc_equiv_istrunc _ (issig_ismonoid _ _ _).

Definition issig_isgroup w x y z : _ <~> @IsGroup w x y z := ltac:(issig).

#[export] Instance ishprop_isgroup `{Funext} w x y z : IsHProp (@IsGroup w x y z)
  := istrunc_equiv_istrunc _ (issig_isgroup _ _ _ _).

End extras.
