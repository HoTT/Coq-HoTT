Require Export
  HoTTClasses.interfaces.canonical_names
  HoTTClasses.misc.util
  HoTTClasses.misc.decision
  HoTTClasses.misc.propholds.

(* 
For various structures we omit declaration of substructures. For example, if we 
say:

Class Setoid_Morphism :=
  { setoidmor_a :> Setoid A
  ; setoidmor_b :> Setoid B
  ; sm_proper :> Proper ((=) ==> (=)) f }.

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
  { apart_symmetric :> Symmetric (≶) 
  ; apart_cotrans :> CoTransitive (≶) 
  ; tight_apart : ∀ x y, ¬x ≶ y ↔ x = y }.

Instance apart_irrefl `{IsApart A} : Irreflexive (≶).
Proof.
intros x ap.
apply (tight_apart x x).
- reflexivity.
- assumption.
Qed.

Arguments tight_apart {A Aap IsApart} _ _.

Section setoid_morphisms.
  Context {A B} {Aap : Apart A} {Bap : Apart B} (f : A → B).

  Class StrongMorphism :=
    { strong_mor_a : IsApart A
    ; strong_mor_b : IsApart B
    ; strong_extensionality : ∀ x y, f x ≶ f y → x ≶ y }.
End setoid_morphisms.

(* HOTT TODO check if this is ok/useful *)
Hint Extern 4 (?f _ = ?f _) => eapply (ap f).

Section setoid_binary_morphisms.
  Context {A B C} {Aap: Apart A} 
    {Bap : Apart B} {Cap : Apart C} (f : A → B → C).

  Class StrongBinaryMorphism :=
    { strong_binary_mor_a : IsApart A
    ; strong_binary_mor_b : IsApart B
    ; strong_binary_mor_c : IsApart C
    ; strong_binary_extensionality : ∀ x₁ y₁ x₂ y₂, f x₁ y₁ ≶ f x₂ y₂ →
                                     x₁ ≶ x₂ ∨ y₁ ≶ y₂ }.
End setoid_binary_morphisms.

(*
Since apartness usually only becomes relevant when considering fields (e.g. the 
real numbers), we do not include it in the lower part of the algebraic hierarchy
(as opposed to CoRN).
*)
Section upper_classes.
  Context (A : Type).

  Class SemiGroup {Aop: SgOp A} :=
    { sg_ass :> Associative (&) }.

  Class CommutativeSemiGroup {Aop : SgOp A} :=
    { comsg_sg :> @SemiGroup Aop
    ; comsg_comm :> Commutative (&) }.

  Class SemiLattice {Aop : SgOp A} :=
    { semilattice_sg :> @CommutativeSemiGroup Aop
    ; semilattice_idempotent :> BinaryIdempotent (&)}.

  Class Monoid {Aop : SgOp A} {Aunit : MonUnit A} :=
    { monoid_semigroup :> SemiGroup
    ; monoid_left_id :> LeftIdentity (&) mon_unit
    ; monoid_right_id :> RightIdentity (&) mon_unit }.

  Class CommutativeMonoid {Aop Aunit} :=
    { commonoid_mon :> @Monoid Aop Aunit
    ; commonoid_commutative :> Commutative (&) }.

  Class Group {Aop Aunit} {Anegate : Negate A} :=
    { group_monoid :> @Monoid Aop Aunit
    ; negate_l :> LeftInverse (&) (-) mon_unit
    ; negate_r :> RightInverse (&) (-) mon_unit }.

  Class BoundedSemiLattice {Aop Aunit} :=
    { bounded_semilattice_mon :> @CommutativeMonoid Aop Aunit
    ; bounded_semilattice_idempotent :> BinaryIdempotent (&)}.

  Class AbGroup {Aop Aunit Anegate} :=
    { abgroup_group :> @Group Aop Aunit Anegate
    ; abgroup_commutative :> Commutative (&) }.

  Context {Aplus : Plus A} {Amult : Mult A} {Azero : Zero A} {Aone : One A}.

  Class SemiRing :=
    { semiplus_monoid :> @CommutativeMonoid plus_is_sg_op zero_is_mon_unit
    ; semimult_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; semiring_distr :> LeftDistribute (.*.) (+)
    ; semiring_left_absorb :> LeftAbsorb (.*.) 0 }.

  Context {Anegate : Negate A}.

  Class Ring :=
    { ring_group :> @AbGroup plus_is_sg_op zero_is_mon_unit _
    ; ring_monoid :> @CommutativeMonoid mult_is_sg_op one_is_mon_unit
    ; ring_dist :> LeftDistribute (.*.) (+) }.

  (* For now, we follow CoRN/ring_theory's example in having Ring and SemiRing
    require commutative multiplication. *)

  Class IntegralDomain :=
    { intdom_ring : Ring 
    ; intdom_nontrivial : PropHolds (1 ≠ 0)
    ; intdom_nozeroes :> NoZeroDivisors A }.

  (* We do not include strong extensionality for (-) and (/) because it can de derived *)
  Class Field {Aap: Apart A} {Arecip: Recip A} :=
    { field_ring :> Ring
    ; field_apart :> IsApart A
    ; field_plus_ext :> StrongBinaryMorphism (+)
    ; field_mult_ext :> StrongBinaryMorphism (.*.)
    ; field_nontrivial : PropHolds (1 ≶ 0)
    ; recip_inverse : ∀ x, x.1 // x = 1 }.

  (* We let /0 = 0 so properties as Injective (/), f (/x) = / (f x), / /x = x, /x * /y = /(x * y) 
    hold without any additional assumptions *)
  Class DecField {Adec_recip : DecRecip A} :=
    { decfield_ring :> Ring
    ; decfield_nontrivial : PropHolds (1 ≠ 0)
    ; dec_recip_0 : /0 = 0
    ; dec_recip_inverse : ∀ x, x ≠ 0 → x / x = 1 }.
End upper_classes.

(* Due to bug #2528 *)
Hint Extern 4 (PropHolds (1 ≠ 0)) => eapply @intdom_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≶ 0)) => eapply @field_nontrivial : typeclass_instances.
Hint Extern 5 (PropHolds (1 ≠ 0)) => eapply @decfield_nontrivial : typeclass_instances.

(* 
For a strange reason Ring instances of Integers are sometimes obtained by
Integers -> IntegralDomain -> Ring and sometimes directly. Making this an
instance with a low priority instead of using intdom_ring:> Ring forces Coq to
take the right way 
*)
Hint Extern 10 (Ring _) => apply @intdom_ring : typeclass_instances.

Arguments recip_inverse {A Aplus Amult Azero Aone Anegate Aap Arecip Field} _.
Arguments dec_recip_inverse {A Aplus Amult Azero Aone Anegate Adec_recip DecField} _ _.
Arguments dec_recip_0 {A Aplus Amult Azero Aone Anegate Adec_recip DecField}.

Section lattice.
  Context A {Ajoin: Join A} {Ameet: Meet A} {Abottom : Bottom A}.

  Class JoinSemiLattice := 
    join_semilattice :> @SemiLattice A join_is_sg_op.
  Class BoundedJoinSemiLattice := 
    bounded_join_semilattice :> @BoundedSemiLattice A join_is_sg_op bottom_is_mon_unit.
  Class MeetSemiLattice := 
    meet_semilattice :> @SemiLattice A meet_is_sg_op.

  Class Lattice := 
    { lattice_join :> JoinSemiLattice
    ; lattice_meet :> MeetSemiLattice
    ; join_meet_absorption :> Absorption (⊔) (⊓) 
    ; meet_join_absorption :> Absorption (⊓) (⊔)}.

  Class DistributiveLattice := 
    { distr_lattice_lattice :> Lattice
    ; join_meet_distr_l :> LeftDistribute (⊔) (⊓) }.
End lattice.

Class Category O `{!Arrows O} `{!CatId O} `{!CatComp O} :=
  { comp_assoc :> ArrowsAssociative O
  ; id_l :> ∀ x y, LeftIdentity (comp x y y) cat_id
  ; id_r :> ∀ x y, RightIdentity (comp x x y) cat_id }.

(* todo: use my comp everywhere *)
Arguments comp_assoc {O arrows CatId CatComp Category w x y z} _ _ _ : rename.

Section morphism_classes.
  Context {A B : Type}.

  Class SemiGroup_Morphism {Aop Bop} (f : A → B) :=
    { sgmor_a : @SemiGroup A Aop
    ; sgmor_b : @SemiGroup B Bop
    ; preserves_sg_op : ∀ x y, f (x & y) = f x & f y }.

  Class JoinSemiLattice_Morphism {Ajoin Bjoin} (f : A → B) :=
    { join_slmor_a : @JoinSemiLattice A Ajoin
    ; join_slmor_b : @JoinSemiLattice B Bjoin
    ; join_slmor_sgmor :> @SemiGroup_Morphism join_is_sg_op join_is_sg_op f }.

  Class MeetSemiLattice_Morphism {Ameet Bmeet} (f : A → B) :=
    { meet_slmor_a : @MeetSemiLattice A Ameet
    ; meet_slmor_b : @MeetSemiLattice B Bmeet
    ; meet_slmor_sgmor :> @SemiGroup_Morphism meet_is_sg_op meet_is_sg_op f }.

  Class Monoid_Morphism {Aunit Bunit Aop Bop} (f : A → B) :=
    { monmor_a : @Monoid A Aop Aunit
    ; monmor_b : @Monoid B Bop Bunit
    ; monmor_sgmor :> SemiGroup_Morphism f
    ; preserves_mon_unit : f mon_unit = mon_unit }.

  Class BoundedJoinSemiLattice_Morphism {Abottom Bbottom Ajoin Bjoin} (f : A → B) :=
    { bounded_join_slmor_a : @BoundedJoinSemiLattice A Ajoin Abottom
    ; bounded_join_slmor_b : @BoundedJoinSemiLattice B Bjoin Bbottom
    ; bounded_join_slmor_monmor :> @Monoid_Morphism bottom_is_mon_unit bottom_is_mon_unit join_is_sg_op join_is_sg_op f }.

  Class SemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { semiringmor_a : @SemiRing A Aplus Amult Azero Aone
    ; semiringmor_b : @SemiRing B Bplus Bmult Bzero Bone
    ; semiringmor_plus_mor :> @Monoid_Morphism zero_is_mon_unit zero_is_mon_unit plus_is_sg_op plus_is_sg_op f
    ; semiringmor_mult_mor :> @Monoid_Morphism one_is_mon_unit one_is_mon_unit mult_is_sg_op mult_is_sg_op f }.

  Class Lattice_Morphism {Ajoin Ameet Bjoin Bmeet} (f : A → B) :=
    { latticemor_a : @Lattice A Ajoin Ameet
    ; latticemor_b : @Lattice B Bjoin Bmeet
    ; latticemor_join_mor :> JoinSemiLattice_Morphism f
    ; latticemor_meet_mor :> MeetSemiLattice_Morphism f }.

  Context {Aap : Apart A} {Bap : Apart B}.
  Class StrongSemiRing_Morphism {Aplus Amult Azero Aone Bplus Bmult Bzero Bone} (f : A → B) :=
    { strong_semiringmor_sr_mor :> @SemiRing_Morphism Aplus Amult Azero Aone Bplus Bmult Bzero Bone f
    ; strong_semiringmor_strong_mor :> StrongMorphism f }.
End morphism_classes.

Section jections.
  Context {A B} {Aap : Apart A} 
    {Bap : Apart B} (f : A → B) `{inv : !Inverse f}.

  Class StrongInjective :=
    { strong_injective : ∀ x y, x ≶ y → f x ≶ f y
    ; strong_injective_mor : StrongMorphism f }.

  Class Injective :=
    { injective : ∀ x y, f x = f y → x = y }.

  Class Surjective :=
    { surjective : f ∘ (f ⁻¹) = id (* a.k.a. "split-epi" *) }.

  Class Bijective :=
    { bijective_injective :> Injective
    ; bijective_surjective :> Surjective }.
End jections.
