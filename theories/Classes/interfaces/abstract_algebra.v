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
  { apart_set : IsHSet A
  ; apart_mere : is_mere_relation _ apart
  ; apart_symmetric : Symmetric (≶)
  ; apart_cotrans : CoTransitive (≶)
  ; tight_apart : forall x y, ~(x ≶ y) <-> x = y }.
#[export] Existing Instances
  apart_set
  apart_mere
  apart_symmetric
  apart_cotrans.

Global Instance apart_irrefl `{IsApart A} : Irreflexive (≶).
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
    { sg_set : IsHSet A
    ; sg_ass : Associative (.*.) }.
    #[export] Existing Instances sg_set sg_ass.

  Class IsCommutativeSemiGroup {Aop : SgOp A} :=
    { comsg_sg : @IsSemiGroup (.*.)
    ; comsg_comm : Commutative (.*.) }.
  #[export] Existing Instances comsg_sg comsg_comm.

  Class IsSemiLattice {Aop : SgOp A} :=
    { semilattice_sg : @IsCommutativeSemiGroup (.*.)
    ; semilattice_idempotent : BinaryIdempotent (.*.)}.
  #[export] Existing Instances semilattice_sg semilattice_idempotent.

  Class IsMonoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { monoid_semigroup : IsSemiGroup
    ; monoid_left_id : LeftIdentity (.*.) mon_unit
    ; monoid_right_id : RightIdentity (.*.) mon_unit }.
  #[export] Existing Instances
    monoid_semigroup
    monoid_left_id
    monoid_right_id.

  Class IsCommutativeMonoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { commonoid_mon : @IsMonoid (.*.) Aunit
    ; commonoid_commutative : Commutative (.*.) }.
  #[export] Existing Instances
    commonoid_mon
    commonoid_commutative.

  Class IsGroup {Aop : SgOp A} {Aunit : MonUnit A} {Anegate : Negate A} :=
    { group_monoid : @IsMonoid (.*.) Aunit
    ; negate_l : LeftInverse (.*.) (-) mon_unit
    ; negate_r : RightInverse (.*.) (-) mon_unit }.
  #[export] Existing Instances 
    group_monoid
    negate_l
    negate_r.

  Class IsBoundedSemiLattice {Aop : SgOp A} {Aunit : MonUnit A} :=
    { bounded_semilattice_mon : @IsCommutativeMonoid (.*.) Aunit
    ; bounded_semilattice_idempotent : BinaryIdempotent (.*.)}.
  #[export] Existing Instances
    bounded_semilattice_mon
    bounded_semilattice_idempotent.

  Class IsAbGroup {Aop : SgOp A} {Aunit : MonUnit A} {Anegate : Negate A} :=
    { abgroup_group : @IsGroup (.*.) Aunit Anegate
    ; abgroup_commutative : Commutative (.*.) }.
  #[export] Existing Instances abgroup_group abgroup_commutative.

  Close Scope mc_mult_scope.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class IsSemiCRing :=
    { semiplus_monoid : @IsCommutativeMonoid plus_is_sg_op zero_is_mon_unit
    ; semimult_monoid : @IsCommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; semiring_distr : LeftDistribute (.*.) (+)
    ; semiring_left_absorb : LeftAbsorb (.*.) 0 }.
  #[export] Existing Instances semiplus_monoid semimult_monoid semiring_distr semiring_left_absorb.

  Context {Anegate : Negate A}.

  Class IsRing := {
    ring_abgroup :: @IsAbGroup plus_is_sg_op zero_is_mon_unit _;
    ring_monoid :: @IsMonoid mult_is_sg_op one_is_mon_unit;
    ring_dist_left :: LeftDistribute (.*.) (+);
    ring_dist_right :: RightDistribute (.*.) (+);
  }.

  Class IsCRing :=
    { cring_group : @IsAbGroup plus_is_sg_op zero_is_mon_unit _
    ; cring_monoid : @IsCommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; cring_dist : LeftDistribute (.*.) (+) }.

  #[export] Existing Instances cring_group cring_monoid cring_dist.
  
  Global Instance isring_iscring : IsCRing -> IsRing.
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
    ; intdom_nozeroes : NoZeroDivisors A }.
  #[export] Existing Instances intdom_nozeroes.

  (* We do not include strong extensionality for (-) and (/)
    because it can de derived *)
  Class IsField {Aap: Apart A} {Arecip: Recip A} :=
    { field_ring : IsCRing
    ; field_apart : IsApart A
    ; field_plus_ext : StrongBinaryExtensionality (+)
    ; field_mult_ext : StrongBinaryExtensionality (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_inverse : forall x, x.1 // x = 1 }.
  #[export] Existing Instances
    field_ring
    field_apart
    field_plus_ext
    field_mult_ext.

  (* We let /0 = 0 so properties as Injective (/),
    f (/x) = / (f x), / /x = x, /x * /y = /(x * y)
    hold without any additional assumptions *)
  Class IsDecField {Adec_recip : DecRecip A} :=
    { decfield_ring : IsCRing
    ; decfield_nontrivial : PropHolds (1 <> 0)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : forall x, x <> 0 -> x / x = 1 }.
  #[export] Existing Instances decfield_ring.

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
    join_semilattice : @IsSemiLattice A join_is_sg_op.
  #[export] Existing Instance join_semilattice.
  Class IsBoundedJoinSemiLattice :=
    bounded_join_semilattice : @IsBoundedSemiLattice A
      join_is_sg_op bottom_is_mon_unit.
  #[export] Existing Instance bounded_join_semilattice.
  Class IsMeetSemiLattice :=
    meet_semilattice : @IsSemiLattice A meet_is_sg_op.
  #[export] Existing Instance meet_semilattice.
  Class IsBoundedMeetSemiLattice :=
    bounded_meet_semilattice : @IsBoundedSemiLattice A
      meet_is_sg_op top_is_mon_unit.
  #[export] Existing Instance bounded_meet_semilattice.


  Class IsLattice :=
    { lattice_join : IsJoinSemiLattice
    ; lattice_meet : IsMeetSemiLattice
    ; join_meet_absorption : Absorption (⊔) (⊓)
    ; meet_join_absorption : Absorption (⊓) (⊔) }.
  #[export] Existing Instances
    lattice_join
    lattice_meet
    join_meet_absorption
    meet_join_absorption.

  Class IsBoundedLattice :=
    { boundedlattice_join : IsBoundedJoinSemiLattice
    ; boundedlattice_meet : IsBoundedMeetSemiLattice
    ; boundedjoin_meet_absorption : Absorption (⊔) (⊓)
    ; boundedmeet_join_absorption : Absorption (⊓) (⊔)}.
  #[export] Existing Instances
    boundedlattice_join
    boundedlattice_meet
    boundedjoin_meet_absorption
    boundedmeet_join_absorption.


  Class IsDistributiveLattice :=
    { distr_lattice_lattice : IsLattice
    ; join_meet_distr_l : LeftDistribute (⊔) (⊓) }.
  #[export] Existing Instances distr_lattice_lattice join_meet_distr_l.
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
    { monmor_sgmor : IsSemiGroupPreserving f
    ; monmor_unitmor : IsUnitPreserving f }.
  #[export] Existing Instances monmor_sgmor monmor_unitmor.
  End sgmorphism_classes.

  Section ringmorphism_classes.
  Context {A B : Type} {Aplus : Plus A} {Bplus : Plus B}
    {Amult : Mult A} {Bmult : Mult B} {Azero : Zero A} {Bzero : Zero B}
    {Aone : One A} {Bone : One B}.

  Class IsSemiRingPreserving (f : A -> B) :=
    { semiringmor_plus_mor : @IsMonoidPreserving A B
        plus_is_sg_op plus_is_sg_op zero_is_mon_unit zero_is_mon_unit f
    ; semiringmor_mult_mor : @IsMonoidPreserving A B
        mult_is_sg_op mult_is_sg_op one_is_mon_unit one_is_mon_unit f }.
  #[export] Existing Instances semiringmor_plus_mor semiringmor_mult_mor.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class IsSemiRingStrongPreserving (f : A -> B) :=
    { strong_semiringmor_sr_mor : IsSemiRingPreserving f
    ; strong_semiringmor_strong_mor : StrongExtensionality f }.
  #[export] Existing Instances strong_semiringmor_sr_mor strong_semiringmor_strong_mor.
  End ringmorphism_classes.

  Section latticemorphism_classes.
  Context {A B : Type} {Ajoin : Join A} {Bjoin : Join B}
    {Ameet : Meet A} {Bmeet : Meet B}.

  Class IsJoinPreserving (f : A -> B) :=
    join_slmor_sgmor : @IsSemiGroupPreserving A B join_is_sg_op join_is_sg_op f.
  #[export] Existing Instances join_slmor_sgmor.

  Class IsMeetPreserving (f : A -> B) :=
    meet_slmor_sgmor : @IsSemiGroupPreserving A B meet_is_sg_op meet_is_sg_op f.
  #[export] Existing Instances meet_slmor_sgmor.

  Context {Abottom : Bottom A} {Bbottom : Bottom B}.
  Class IsBoundedJoinPreserving (f : A -> B) := bounded_join_slmor_monmor
      : @IsMonoidPreserving A B join_is_sg_op join_is_sg_op
         bottom_is_mon_unit bottom_is_mon_unit f.
  #[export] Existing Instances bounded_join_slmor_monmor.

  Class IsLatticePreserving (f : A -> B) :=
    { latticemor_join_mor : IsJoinPreserving f
    ; latticemor_meet_mor : IsMeetPreserving f }.
  #[export] Existing Instances
    latticemor_join_mor
    latticemor_meet_mor.
  End latticemorphism_classes.
End morphism_classes.

Section id_mor.
  Context `{SgOp A} `{MonUnit A}.

  Global Instance id_sg_morphism : IsSemiGroupPreserving (@id A).
  Proof.
    split.
  Defined.

  Global Instance id_monoid_morphism : IsMonoidPreserving (@id A).
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
    - apply _.
    - red;unfold Compose.
      etransitivity;[|apply (preserves_mon_unit (f:=g))].
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
    refine (_ @ _ @ _ @ _)^.
    - apply fp.
    (* We could use [apply ap2; apply eisretr] here, but it is convenient
       to have things in terms of ap. *)
    - refine (ap (fun z => sg_op z _) _); apply eisretr.
    - refine (ap (fun z => sg_op _ z) _); apply eisretr.
    - symmetry; apply eisretr.
  Defined.

  Local Instance invert_monoid_morphism :
    forall `{!IsEquiv f}, IsMonoidPreserving f -> IsMonoidPreserving (f^-1).
  Proof.
    intros;split.
    - apply _.
    - apply (equiv_inj f).
      refine (_ @ _).
      + apply eisretr.
      + symmetry; apply preserves_mon_unit.
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


Global Instance ishprop_issemigrouppreserving `{Funext} {A B : Type} `{IsHSet B}
  `{SgOp A} `{SgOp B} {f : A -> B} : IsHProp (IsSemiGroupPreserving f).
Proof.
  unfold IsSemiGroupPreserving; exact _.
Defined.

Definition issig_IsSemiRingPreserving {A B : Type}
  `{Plus A, Plus B, Mult A, Mult B, Zero A, Zero B, One A, One B} {f : A -> B}
  : _ <~> IsSemiRingPreserving f := ltac:(issig).

Definition issig_IsMonoidPreserving {A B : Type} `{SgOp A} `{SgOp B}
  `{MonUnit A} `{MonUnit B} {f : A -> B} : _ <~> IsMonoidPreserving f
  := ltac:(issig).

Global Instance ishprop_ismonoidpreserving `{Funext} {A B : Type} `{SgOp A}
  `{SgOp B} `{IsHSet B} `{MonUnit A} `{MonUnit B} (f : A -> B)
  : IsHProp (IsMonoidPreserving f).
Proof.
  srapply (istrunc_equiv_istrunc _ issig_IsMonoidPreserving).
  srapply (istrunc_equiv_istrunc _ (equiv_sigma_prod0 _ _)^-1).
  srapply istrunc_prod.
  unfold IsUnitPreserving.
  exact _.
Defined.

Global Instance ishprop_issemiringpreserving `{Funext} {A B : Type} `{IsHSet B}
  `{Plus A, Plus B, Mult A, Mult B, Zero A, Zero B, One A, One B}
  (f : A -> B)
  : IsHProp (IsSemiRingPreserving f).
Proof.
  snrapply (istrunc_equiv_istrunc _ issig_IsSemiRingPreserving).
  exact _.
Defined.

Definition issig_issemigroup x y : _ <~> @IsSemiGroup x y := ltac:(issig).

Global Instance ishprop_issemigroup `{Funext}
  : forall x y, IsHProp (@IsSemiGroup x y).
Proof.
  intros x y; apply istrunc_S; intros a b.
  rewrite <- (eisretr (issig_issemigroup x y) a).
  rewrite <- (eisretr (issig_issemigroup x y) b).
  set (a' := (issig_issemigroup x y)^-1 a).
  set (b' := (issig_issemigroup x y)^-1 b).
  clearbody a' b'; clear a b.
  srapply (contr_equiv _ (ap (issig_issemigroup x y))).
  rewrite <- (eissect (equiv_sigma_prod0 _ _) a').
  rewrite <- (eissect (equiv_sigma_prod0 _ _) b').
  set (a := equiv_sigma_prod0 _ _ a').
  set (b := equiv_sigma_prod0 _ _ b').
  clearbody a b; clear a' b'.
  srapply (contr_equiv _ (ap (equiv_sigma_prod0 _ _)^-1)).
  srapply (contr_equiv _ (equiv_path_prod _ _)).
  srapply contr_prod.
  destruct a as [a' a], b as [b' b].
  do 3 (nrefine (contr_equiv' _ (@equiv_path_forall H _ _ _ _));
  nrefine (@contr_forall H _ _ _); intro).
  exact _.
Defined.

Definition issig_ismonoid x y z : _ <~> @IsMonoid x y z := ltac:(issig).

Global Instance ishprop_ismonoid `{Funext} x y z : IsHProp (@IsMonoid x y z).
Proof.
  apply istrunc_S.
  intros a b.
  rewrite <- (eisretr (issig_ismonoid x y z) a).
  rewrite <- (eisretr (issig_ismonoid x y z) b).
  set (a' := (issig_ismonoid x y z)^-1 a).
  set (b' := (issig_ismonoid x y z)^-1 b).
  clearbody a' b'; clear a b.
  srapply (contr_equiv _ (ap (issig_ismonoid x y z))).
  rewrite <- (eissect (equiv_sigma_prod0 _ _) a').
  rewrite <- (eissect (equiv_sigma_prod0 _ _) b').
  set (a := equiv_sigma_prod0 _ _ a').
  set (b := equiv_sigma_prod0 _ _ b').
  clearbody a b; clear a' b'.
  srapply (contr_equiv _ (ap (equiv_sigma_prod0 _ _)^-1)).
  srapply (contr_equiv _ (equiv_path_prod _ _)).
  srapply contr_prod.
  destruct a as [a' a], b as [b' b]; cbn.
  rewrite <- (eissect (equiv_sigma_prod0 _ _) a).
  rewrite <- (eissect (equiv_sigma_prod0 _ _) b).
  set (a'' := equiv_sigma_prod0 _ _ a).
  set (b'' := equiv_sigma_prod0 _ _ b).
  clearbody a'' b''; clear a b.
  srapply (contr_equiv _ (ap (equiv_sigma_prod0 _ _)^-1)).
  srapply (contr_equiv _ (equiv_path_prod _ _)).
  destruct a'' as [a a''], b'' as [b b'']; cbn.
  snrapply contr_prod.
  all: srapply contr_paths_contr.
  all: srapply contr_inhabited_hprop.
  all: srapply istrunc_forall.
Defined.

Definition issig_isgroup w x y z : _ <~> @IsGroup w x y z := ltac:(issig).

Global Instance ishprop_isgroup `{Funext} w x y z : IsHProp (@IsGroup w x y z).
Proof.
  apply istrunc_S.
  intros a b.
  rewrite <- (eisretr (issig_isgroup w x y z) a).
  rewrite <- (eisretr (issig_isgroup w x y z) b).
  set (a' := (issig_isgroup w x y z)^-1 a).
  set (b' := (issig_isgroup w x y z)^-1 b).
  clearbody a' b'; clear a b.
  srapply (contr_equiv _ (ap (issig_isgroup w x y z))).
  rewrite <- (eissect (equiv_sigma_prod0 _ _) a').
  rewrite <- (eissect (equiv_sigma_prod0 _ _) b').
  set (a := equiv_sigma_prod0 _ _ a').
  set (b := equiv_sigma_prod0 _ _ b').
  clearbody a b; clear a' b'.
  srapply (contr_equiv _ (ap (equiv_sigma_prod0 _ _)^-1)).
  srapply (contr_equiv _ (equiv_path_prod _ _)).
  srapply contr_prod.
  destruct a as [a' a], b as [b' b]; cbn.
  rewrite <- (eissect (equiv_sigma_prod0 _ _) a).
  rewrite <- (eissect (equiv_sigma_prod0 _ _) b).
  set (a'' := equiv_sigma_prod0 _ _ a).
  set (b'' := equiv_sigma_prod0 _ _ b).
  clearbody a'' b''; clear a b.
  srapply (contr_equiv _ (ap (equiv_sigma_prod0 _ _)^-1)).
  srapply (contr_equiv _ (equiv_path_prod _ _)).
  destruct a'' as [a a''], b'' as [b b'']; cbn.
  srapply contr_prod.
  all: srapply contr_paths_contr.
  all: srapply contr_inhabited_hprop.
  all: srapply istrunc_forall.
Defined.

End extras.
