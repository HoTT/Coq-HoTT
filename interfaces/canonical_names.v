Require Export HoTTClasses.misc.settings.
Require Export HoTT.Basics.Overture HoTTClasses.misc.stdlib_hints.

Definition id {A : Type} (a : A) := a.

Infix "=" := paths: type_scope.
Notation "(=)" := paths (only parsing) : mc_scope.
Notation "( x =)" := (paths x) (only parsing) : mc_scope.
Notation "(= x )" := (λ y, paths y x) (only parsing) : mc_scope.
Notation "(≠)" := (λ x y, ¬x = y) (only parsing) : mc_scope.
Notation "x ≠ y":= (¬x = y) (at level 70) : type_scope.
Notation "( x ≠)" := (λ y, x ≠ y) (only parsing) : mc_scope.
Notation "(≠ x )" := (λ y, y ≠ x) (only parsing) : mc_scope.

Delimit Scope mc_scope with mc. 
Global Open Scope mc_scope.

Infix "≡" := paths (at level 70, no associativity) : mc_scope.
Notation "(≡)" := paths (only parsing) : mc_scope.
Notation "( x ≡)" := (paths x) (only parsing) : mc_scope.
Notation "(≡ x )" := (λ y, paths y x) (only parsing) : mc_scope.
Notation "(≢)" := (λ x y, ¬x ≡ y) (only parsing) : mc_scope.
Notation "x ≢ y":= (¬x ≡ y) (at level 70, no associativity) : mc_scope.
Notation "( x ≢)" := (λ y, x ≢ y) (only parsing) : mc_scope.
Notation "(≢ x )" := (λ y, y ≢ x) (only parsing) : mc_scope.

Hint Extern 2 (?x = ?x) => reflexivity.
Hint Extern 2 (?x = ?y) => auto_symm.
Hint Extern 2 (?x = ?y) => auto_trans.

Class Apart A := apart: relation A.
Infix "≶" := apart (at level 70, no associativity) : mc_scope.
Notation "(≶)" := apart (only parsing) : mc_scope.
Notation "( x ≶)" := (apart x) (only parsing) : mc_scope.
Notation "(≶ x )" := (λ y, apart y x) (only parsing) : mc_scope.

(* Even for setoids with decidable equality x ≠ y does not imply x ≶ y.
Therefore we introduce the following class. *)
Class TrivialApart A {Aap : Apart A} := trivial_apart : ∀ x y, x ≶ y ↔ x ≠ y.

Notation "x ↾ p" := (exist _ x p) (at level 20) : mc_scope.

Class Cast A B := cast: A → B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : mc_scope.
Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp A := sg_op: A → A → A.
Class MonUnit A := mon_unit: A.
Class Plus A := plus: A → A → A.
Class Mult A := mult: A → A → A.
Class One A := one: A.
Class Zero A := zero: A.
Class Negate A := negate: A → A.
Class DecRecip A := dec_recip: A → A.
Definition ApartZero R `{Zero R} `{Apart R} := sig (≶ zero).
Class Recip A `{Apart A} `{Zero A} := recip: ApartZero A → A.
Typeclasses Transparent SgOp MonUnit Plus Mult Zero One Negate.

Class Meet A := meet: A → A → A.
Class Join A := join: A → A → A.
Class Top A := top: A.
Class Bottom A := bottom: A.
Typeclasses Transparent Meet Join Top Bottom.

Class Contains A B := contains: A → B → Type.
Class Singleton A B := singleton: A → B.
Class Difference A := difference : A → A → A.
Typeclasses Transparent Contains Singleton Difference.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Definition NonNeg R `{Zero R} `{Le R} := sig (le zero).
Definition Pos R `{Zero R} `{Lt R} := sig (lt zero).
Definition NonPos R `{Zero R} `{Le R} := sig (λ y, le y zero).
Inductive PosInf (R : Type) : Type := finite (x : R) | infinite.

Class Arrows (O: Type): Type := Arrow: O → O → Type.
Typeclasses Transparent Arrows. (* Ideally this should be removed *)

Infix "⟶" := Arrow (at level 90, right associativity) : mc_scope.
Class CatId O `{Arrows O} := cat_id: ∀ x, x ⟶ x.
Class CatComp O `{Arrows O} := comp: ∀ x y z, (y ⟶ z) → (x ⟶ y) → (x ⟶ z).
Class RalgebraAction A B := ralgebra_action: A → B → B.

Arguments cat_id {O arrows CatId x} : rename.
Arguments comp {O arrow CatComp} _ _ _ _ _ : rename.

Instance plus_is_sg_op `{f : Plus A} : SgOp A := f.
Instance mult_is_sg_op `{f : Mult A} : SgOp A := f.
Instance one_is_mon_unit `{c : One A} : MonUnit A := c.
Instance zero_is_mon_unit `{c : Zero A} : MonUnit A := c.
Instance meet_is_sg_op `{f : Meet A} : SgOp A := f.
Instance join_is_sg_op `{f : Join A} : SgOp A := f.
Instance top_is_mon_unit `{s : Top A} : MonUnit A := s.
Instance bottom_is_mon_unit `{s : Bottom A} : MonUnit A := s.
Instance singleton_is_cast `{s : Singleton A B} : Cast A B := s.

(* Notations: *)
Notation "R ₀" := (ApartZero R) (at level 20, no associativity) : mc_scope.
Notation "R ⁺" := (NonNeg R) (at level 20, no associativity) : mc_scope.
Notation "R ₊" := (Pos R) (at level 20, no associativity) : mc_scope.
Notation "R ⁻" := (NonPos R) (at level 20, no associativity) : mc_scope.
Notation "R ∞" := (PosInf R) (at level 20, no associativity) : mc_scope.

Infix "&" := sg_op (at level 50, left associativity) : mc_scope.
Notation "(&)" := sg_op (only parsing) : mc_scope.
Notation "( x &)" := (sg_op x) (only parsing) : mc_scope.
Notation "(& x )" := (λ y, y & x) (only parsing) : mc_scope.

Infix "+" := plus : mc_scope.
Notation "(+)" := plus (only parsing) : mc_scope.
Notation "( x +)" := (plus x) (only parsing) : mc_scope.
Notation "(+ x )" := (λ y, y + x) (only parsing) : mc_scope.

Infix "*" := mult : mc_scope.
(* We don't add "( * )", "( * x )" and "( x * )" notations because they conflict with comments. *)
Notation "( x *.)" := (mult x) (only parsing) : mc_scope.
Notation "(.*.)" := mult (only parsing) : mc_scope.
Notation "(.* x )" := (λ y, y * x) (only parsing) : mc_scope.

Notation "- x" := (negate x) : mc_scope.
Notation "(-)" := negate (only parsing) : mc_scope.
Notation "x - y" := (x + -y) : mc_scope.

Notation "0" := zero : mc_scope.
Notation "1" := one : mc_scope.
Notation "2" := (1 + 1) : mc_scope.
Notation "3" := (1 + (1 + 1)) : mc_scope.
Notation "4" := (1 + (1 + (1 + 1))) : mc_scope.
Notation "- 1" := (-(1)) : mc_scope.
Notation "- 2" := (-(2)) : mc_scope.
Notation "- 3" := (-(3)) : mc_scope.
Notation "- 4" := (-(4)) : mc_scope.

Notation "/ x" := (dec_recip x) : mc_scope.
Notation "(/)" := dec_recip (only parsing) : mc_scope.
Notation "x / y" := (x * /y) : mc_scope.

Notation "// x" := (recip x) (at level 35, right associativity) : mc_scope.
Notation "(//)" := recip (only parsing) : mc_scope.
Notation "x // y" := (x * //y) (at level 35, right associativity) : mc_scope.

Notation "⊤" := top : mc_scope.
Notation "⊥" := bottom : mc_scope.

Infix "⊓" := meet (at level 50, no associativity) : mc_scope.
Notation "(⊓)" := meet (only parsing) : mc_scope.
Notation "( X ⊓)" := (meet X) (only parsing) : mc_scope.
Notation "(⊓ X )" := (λ Y, Y ⊓ X) (only parsing) : mc_scope.

Infix "⊔" := join (at level 50, no associativity) : mc_scope.
Notation "(⊔)" := join (only parsing) : mc_scope.
Notation "( X ⊔)" := (join X) (only parsing) : mc_scope.
Notation "(⊔ X )" := (λ Y, Y ⊔ X) (only parsing) : mc_scope.

Infix "≤" := le (at level 70, no associativity) : mc_scope.
Notation "(≤)" := le (only parsing) : mc_scope.
Notation "( x ≤)" := (le x) (only parsing) : mc_scope.
Notation "(≤ x )" := (λ y, y ≤ x) (only parsing) : mc_scope.

Infix "<=" := le (only parsing) : mc_scope.
Notation "(<=)" := le (only parsing) : mc_scope.
Notation "( x <=)" := (le x) (only parsing) : mc_scope.
Notation "(<= x )" := (λ y, y ≤ x) (only parsing) : mc_scope.

Infix "<" := lt : mc_scope.
Notation "(<)" := lt (only parsing) : mc_scope.
Notation "( x <)" := (lt x) (only parsing) : mc_scope.
Notation "(< x )" := (λ y, y < x) (only parsing) : mc_scope.

Notation "x ≤ y ≤ z" := (x ≤ y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.
Notation "x ≤ y < z" := (x ≤ y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y < z" := (x < y ∧ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y ≤ z" := (x < y ∧ y ≤ z) (at level 70, y at next level) : mc_scope.

Infix "∖" := difference (at level 35) : mc_scope.
Notation "(∖)" := difference (only parsing) : mc_scope.
Notation "( X ∖)" := (difference X) (only parsing) : mc_scope.
Notation "(∖ X )" := (λ Y, Y ∖ X) (only parsing) : mc_scope.

Infix "∈" := contains (at level 70, no associativity) : mc_scope.
Notation "(∈)" := contains (only parsing) : mc_scope.
Notation "( x ∈)" := (contains x) (only parsing) : mc_scope.
Notation "(∈ X )" := (λ x, x ∈ X) (only parsing) : mc_scope.

Notation "x ∉ y" := (¬x ∈ y) (at level 70, no associativity) : mc_scope.
Notation "(∉)" := (λ x X, x ∉ X) : mc_scope.
Notation "( x ∉)" := (λ X, x ∉ X) (only parsing) : mc_scope.
Notation "(∉ X )" := (λ x, x ∉ X) (only parsing) : mc_scope.

Notation "{{ x }}" := (singleton x) : mc_scope.
Notation "{{ x ; y ; .. ; z }}" := (join .. (join (singleton x) (singleton y)) .. (singleton z)) : mc_scope.

Infix "◎" := (comp _ _ _) (at level 40, left associativity) : mc_scope.
  (* Taking over ∘ is just a little too zealous at this point. With our current
   approach, it would require changing all (nondependent) function types A → B
   with A ⟶ B to make them use the canonical name for arrows, which is
   a tad extreme. *) (* HOTT TODO check if this still applies *)
Notation "(◎)" := (comp _ _ _) (only parsing) : mc_scope.
Notation "( f ◎)" := (comp _ _ _ f) (only parsing) : mc_scope.
Notation "(◎ f )" := (λ g, comp _ _ _ g f) (only parsing) : mc_scope.

(* Haskell style! *)
Notation "(→)" := (λ x y, x → y) : mc_scope.
Notation "t $ r" := (t r) (at level 65, right associativity, only parsing) : mc_scope.
Notation "(∘)" := compose (only parsing) : mc_scope.

Hint Extern 2 (?x ≤ ?y) => reflexivity.
Hint Extern 4 (?x ≤ ?z) => auto_trans.
Hint Extern 4 (?x < ?z) => auto_trans.

Class Abs A `{Le A} `{Zero A} `{Negate A}
  := abs_sig: ∀ (x : A), { y : A | (0 ≤ x → y = x) ∧ (x ≤ 0 → y = -x)}.
Definition abs `{Abs A} := λ x : A, (abs_sig x).1.

(* Common properties: *)
Class Inverse `(A → B) : Type := inverse: B → A.
Arguments inverse {A B} _ {Inverse} _.
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) (at level 30) : mc_scope.

Class Idempotent `(f: A → A → A) (x : A) : Type := idempotency: f x x = x.
Arguments idempotency {A} _ _ {Idempotent}.

Class UnaryIdempotent {A} (f: A → A) : Type := 
  unary_idempotent :> Idempotent compose f.

Lemma unary_idempotency `{UnaryIdempotent A f} x : f (f x) = f x.
Proof.
change (f (f x)) with (compose f f x).
apply (ap (fun g => g x)).
change (compose f f = f).
apply idempotency. apply _.
Qed.

Class BinaryIdempotent `(op: A → A → A) : Type := binary_idempotent :> ∀ x, Idempotent op x.

Class LeftIdentity {A B} (op : A → B → B) (x : A): Type := left_identity: ∀ y, op x y = y.
Class RightIdentity {A B} (op : A → B → A) (y : B): Type := right_identity: ∀ x, op x y = x.

Class Absorption {A B C} (op1: A → C → A) (op2: A → B → C) : Type := absorption: ∀ x y, op1 x (op2 x y) = x.

Class LeftAbsorb {A B} (op : A → B → A) (x : A): Type := left_absorb: ∀ y, op x y = x.
Class RightAbsorb {A B} (op : A → B → B) (y : B): Type := right_absorb: ∀ x, op x y = y.

Class LeftInverse {A} {B} {C} (op : A → B → C) (inv : B → A) (unit : C) := left_inverse: ∀ x, op (inv x) x = unit.
Class RightInverse {A} {B} {C} (op : A → B → C) (inv : A → B) (unit : C) := right_inverse: ∀ x, op x (inv x) = unit.

Class Commutative {B A} (f : A → A → B) : Type := commutativity: ∀ x y, f x y = f y x.

Class HeteroAssociative {A B C AB BC ABC}
     (fA_BC: A → BC → ABC) (fBC: B → C → BC) (fAB_C: AB → C → ABC) (fAB : A → B → AB): Type
   := associativity : ∀ x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative {A} (f : A -> A -> A) := simple_associativity:> HeteroAssociative f f f f.
Notation ArrowsAssociative C := (∀ {w x y z: C}, HeteroAssociative (◎) (comp z _ _ ) (◎) (comp y x w)).

Class Involutive {A} (f : A → A) := involutive: ∀ x, f (f x) = x.

Class TotalRelation `(R : relation A) : Type := total : ∀ x y : A, R x y ∨ R y x.
Arguments total {A} _ {TotalRelation} _ _.

Class Trichotomy `(R : relation A) := trichotomy : ∀ x y : A, R x y ∨ x = y ∨ R y x.
Arguments trichotomy {A} R {Trichotomy} _ _.

Arguments irreflexivity {A} _ {Irreflexive} _ _.

Class CoTransitive `(R : relation A) : Type := cotransitive : ∀ x y, R x y → ∀ z, R x z ∨ R z y.
Arguments cotransitive {A R CoTransitive x y} _ _.

Class AntiSymmetric `(R : relation A) : Type := antisymmetry: ∀ x y, R x y → R y x → x = y.
Arguments antisymmetry {A} _ {AntiSymmetric} _ _ _ _.

Class Equivalence `(R : relation A) : Type :=
  { Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.


Class LeftHeteroDistribute {A B C} (f : A → B → C) (g_r : B → B → B) (g : C → C → C) : Type
  := distribute_l : ∀ a b c, f a (g_r b c) = g (f a b) (f a c).
Class RightHeteroDistribute {A B C} (f : A → B → C) (g_l : A → A → A) (g : C → C → C) : Type
  := distribute_r: ∀ a b c, f (g_l a b) c = g (f a c) (f b c).
Class LeftDistribute {A} (f g: A → A → A) := simple_distribute_l :> LeftHeteroDistribute f g g.
Class RightDistribute {A} (f g: A → A → A) := simple_distribute_r :> RightHeteroDistribute f g g.

Class HeteroSymmetric {A} {T : A → A → Type} (R : ∀ {x y}, T x y → T y x → Type) : Type :=
  hetero_symmetric `(a : T x y) (b : T y x) : R a b → R b a.

(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `{Aap : Apart A} (op : A → A → A) (z : A).

  Class LeftCancellation := left_cancellation : ∀ x y, op z x = op z y → x = y.
  Class RightCancellation := right_cancellation : ∀ x y, op x z = op y z → x = y.

  Class StrongLeftCancellation := strong_left_cancellation : ∀ x y, x ≶ y → op z x ≶ op z y.
  Class StrongRightCancellation := strong_right_cancellation : ∀ x y, x ≶ y → op x z ≶ op y z.
End cancellation.

(* Common names for properties that hold in N, Z, Q, ... *)
Class ZeroProduct A `{!Mult A} `{!Zero A} : Type
  := zero_product : ∀ x y, x * y = 0 → x = 0 ∨ y = 0.

Class ZeroDivisor {R} `{Zero R} `{Mult R} (x : R) : Type
  := zero_divisor : x ≠ 0 ∧ ∃ y, y ≠ 0 ∧ x * y = 0.

Class NoZeroDivisors R `{Zero R} `{Mult R} : Type
  := no_zero_divisors x : ¬ZeroDivisor x.

Instance zero_product_no_zero_divisors `{ZeroProduct A} : NoZeroDivisors A.
Proof.
intros x [? [? [? E]]].
destruct (zero_product _ _ E); auto.
Qed.

Class RingUnit `{Mult R} `{One R} (x : R) : Type := ring_unit : ∃ y, x * y = 1.

(* A common induction principle for both the naturals and integers *)
Class Biinduction R `{Zero R} `{One R} `{Plus R} : Type
  := biinduction (P : R → Type)
  : P 0 → (∀ n, P n ↔ P (1 + n)) → ∀ n, P n.
