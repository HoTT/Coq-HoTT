Require Export HoTT.Basics.Overture HoTT.Types.Bool HoTT.Basics.Decidable HoTT.Basics.Trunc HoTT.HIT.Truncations.

Declare Scope mc_scope.
Delimit Scope mc_scope with mc.
Global Open Scope mc_scope.

(* 'o' is used for the compose notation. *)
Global Generalizable Variables
  A B C D E F G H I J K L M N O P Q R S T U V W X Y Z
  a b c d e f g h i j k l m n p q r s t u v w x y z
  Fa Ga
  Fle Flt Nle Nlt Rle Rlt
  R1le R2le
  Alt Blt R1lt R2lt Vlt Zle Zlt
  SR.

Monomorphic Universe Ularge Uhuge.
Monomorphic Constraint Ularge < Uhuge.

Lemma merely_destruct {A} {P : Type} {sP : IsHProp P}
  (x : merely A) : (A -> P) -> P.
Proof.
intros E;revert x.
apply Trunc_ind.
- apply _.
- exact E.
Qed.

Notation " g ∘ f " := (Compose g f)%mc
  (at level 40, left associativity).
Notation "(∘)" := Compose (only parsing) : mc_scope.

Definition id {A : Type} (a : A) := a.

Notation "(=)" := paths (only parsing) : mc_scope.
Notation "( x =)" := (paths x) (only parsing) : mc_scope.
Notation "(= x )" := (fun y => paths y x) (only parsing) : mc_scope.

Notation "(<>)" := (fun x y => ~x = y) (only parsing) : mc_scope.
Notation "( x <>)" := (fun y => x <> y) (only parsing) : mc_scope.
Notation "(<> x )" := (fun y => y <> x) (only parsing) : mc_scope.

Class Apart A := apart: relation A.
Infix "≶" := apart (at level 70, no associativity) : mc_scope.
Notation "(≶)" := apart (only parsing) : mc_scope.
Notation "( x ≶)" := (apart x) (only parsing) : mc_scope.
Notation "(≶ x )" := (fun y => apart y x) (only parsing) : mc_scope.

(* Even for setoids with decidable equality x <> y does not imply x ≶ y.
Therefore we introduce the following class. *)
Class TrivialApart A {Aap : Apart A} :=
  { trivial_apart_prop :> is_mere_relation A apart
  ; trivial_apart : forall x y, x ≶ y <-> x <> y }.

Definition sig_apart `{Apart A} (P: A -> Type) : Apart (sig P) := fun x y => x.1 ≶ y.1.
Hint Extern 10 (Apart (sig _)) => apply @sig_apart : typeclass_instances.

Class Cast A B := cast: A -> B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) (at level 20) : mc_scope.
Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp A := sg_op: A -> A -> A.
Class MonUnit A := mon_unit: A.
Class Plus A := plus: A -> A -> A.
Class Mult A := mult: A -> A -> A.
Class One A := one: A.
Class Zero A := zero: A.
Class Negate A := negate: A -> A.
Class DecRecip A := dec_recip: A -> A.
Definition ApartZero R `{Zero R} `{Apart R} := sig (≶ zero).
Class Recip A `{Apart A} `{Zero A} := recip: ApartZero A -> A.
Typeclasses Transparent SgOp MonUnit Plus Mult Zero One Negate.

Class Meet A := meet: A -> A -> A.
Class Join A := join: A -> A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.
Typeclasses Transparent Meet Join Top Bottom.

Class Le A := le: relation A.
Class Lt A := lt: relation A.
Typeclasses Transparent Le Lt.

Definition NonNeg R `{Zero R} `{Le R} := sig (le zero).
Definition Pos R `{Zero R} `{Lt R} := sig (lt zero).
Definition NonPos R `{Zero R} `{Le R} := sig (fun y => le y zero).

Instance plus_is_sg_op `{f : Plus A} : SgOp A := f.
Instance mult_is_sg_op `{f : Mult A} : SgOp A := f.
Instance one_is_mon_unit `{c : One A} : MonUnit A := c.
Instance zero_is_mon_unit `{c : Zero A} : MonUnit A := c.
Instance meet_is_sg_op `{f : Meet A} : SgOp A := f.
Instance join_is_sg_op `{f : Join A} : SgOp A := f.
Instance top_is_mon_unit `{s : Top A} : MonUnit A := s.
Instance bottom_is_mon_unit `{s : Bottom A} : MonUnit A := s.

Hint Extern 4 (Apart (ApartZero _)) => apply @sig_apart : typeclass_instances.
Hint Extern 4 (Apart (NonNeg _)) => apply @sig_apart : typeclass_instances.
Hint Extern 4 (Apart (Pos _)) => apply @sig_apart : typeclass_instances.

(* Notations: *)
Infix "&" := sg_op (at level 50, left associativity) : mc_scope.
Notation "(&)" := sg_op (only parsing) : mc_scope.
Notation "( x &)" := (sg_op x) (only parsing) : mc_scope.
Notation "(& x )" := (fun y => y & x) (only parsing) : mc_scope.

Infix "+" := plus : mc_scope.
Notation "(+)" := plus (only parsing) : mc_scope.
Notation "( x +)" := (plus x) (only parsing) : mc_scope.
Notation "(+ x )" := (fun y => y + x) (only parsing) : mc_scope.

Infix "*" := mult : mc_scope.
(* We don't add "( * )", "( * x )" and "( x * )" notations
   because they conflict with comments. *)
Notation "( x *.)" := (mult x) (only parsing) : mc_scope.
Notation "(.*.)" := mult (only parsing) : mc_scope.
Notation "(.* x )" := (fun y => y * x) (only parsing) : mc_scope.

Notation "- x" := (negate x) : mc_scope.
Notation "(-)" := negate (only parsing) : mc_scope.
Notation "x - y" := (x + -y) : mc_scope.

Notation "0" := zero : mc_scope.
Notation "1" := one : mc_scope.
Notation "2" := (1 + 1) : mc_scope.
Notation "3" := (1 + (1 + 1)) : mc_scope.
Notation "4" := (1 + (1 + (1 + 1))) : mc_scope.
Notation "5" := (1 + (1 + (1 + (1 + 1)))) : mc_scope.
Notation "6" := (1 + (1 + (1 + (1 + (1 + 1))))) : mc_scope.
Notation "- 1" := (-(1)) : mc_scope.
Notation "- 2" := (-(2)) : mc_scope.
Notation "- 3" := (-(3)) : mc_scope.
Notation "- 4" := (-(4)) : mc_scope.

Notation "/ x" := (dec_recip x) : mc_scope.
Notation "(/)" := dec_recip (only parsing) : mc_scope.
Notation "x / y" := (x * /y) : mc_scope.

Notation "// x" := (recip x) (at level 40, no associativity) : mc_scope.
Notation "(//)" := recip (only parsing) : mc_scope.
Notation "x // y" := (x * //y) (at level 40, left associativity) : mc_scope.

Notation "⊤" := top : mc_scope.
Notation "⊥" := bottom : mc_scope.

Infix "⊓" := meet (at level 50, no associativity) : mc_scope.
Notation "(⊓)" := meet (only parsing) : mc_scope.
Notation "( X ⊓)" := (meet X) (only parsing) : mc_scope.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : mc_scope.

Infix "⊔" := join (at level 50, no associativity) : mc_scope.
Notation "(⊔)" := join (only parsing) : mc_scope.
Notation "( X ⊔)" := (join X) (only parsing) : mc_scope.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : mc_scope.

Infix "≤" := le (at level 70, no associativity) : mc_scope.
Notation "(≤)" := le (only parsing) : mc_scope.
Notation "( x ≤)" := (le x) (only parsing) : mc_scope.
Notation "(≤ x )" := (fun y => y ≤ x) (only parsing) : mc_scope.

Infix "<=" := le (only parsing) : mc_scope.
Notation "(<=)" := le (only parsing) : mc_scope.
Notation "( x <=)" := (le x) (only parsing) : mc_scope.
Notation "(<= x )" := (fun y => y ≤ x) (only parsing) : mc_scope.

Infix "<" := lt : mc_scope.
Notation "(<)" := lt (only parsing) : mc_scope.
Notation "( x <)" := (lt x) (only parsing) : mc_scope.
Notation "(< x )" := (fun y => y < x) (only parsing) : mc_scope.

Notation "x ≤ y ≤ z" := (x ≤ y /\ y ≤ z) (at level 70, y at next level) : mc_scope.
Notation "x ≤ y < z" := (x ≤ y /\ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y < z" := (x < y /\ y < z) (at level 70, y at next level) : mc_scope.
Notation "x < y ≤ z" := (x < y /\ y ≤ z) (at level 70, y at next level) : mc_scope.

(** It is likely that ≤ and < are transitive (and ≤ reflexive) so inform [auto] of this. *)
Ltac auto_trans := match goal with
                    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
                  end.

Hint Extern 2 (?x ≤ ?y) => reflexivity.
Hint Extern 4 (?x ≤ ?z) => auto_trans.
Hint Extern 4 (?x < ?z) => auto_trans.

Class Abs A `{Le A} `{Zero A} `{Negate A}
  := abs_sig: forall (x : A), { y : A | (0 ≤ x -> y = x) /\ (x ≤ 0 -> y = -x)}.
Definition abs `{Abs A} := fun x : A => (abs_sig x).1.

(* Common properties: *)
Class Inverse `(A -> B) : Type := inverse: B -> A.
Arguments inverse {A B} _ {Inverse} _.
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) (at level 30) : mc_scope.

Class Idempotent `(f: A -> A -> A) (x : A) : Type := idempotency: f x x = x.
Arguments idempotency {A} _ _ {Idempotent}.

Class UnaryIdempotent {A} (f: A -> A) : Type :=
  unary_idempotent :> Idempotent Compose f.

Lemma unary_idempotency `{UnaryIdempotent A f} x : f (f x) = f x.
Proof.
change (f (f x)) with (Compose f f x).
apply (ap (fun g => g x)).
change (Compose f f = f).
apply idempotency. apply _.
Qed.

Class BinaryIdempotent `(op: A -> A -> A) : Type
  := binary_idempotent :> forall x, Idempotent op x.

Class LeftIdentity {A B} (op : A -> B -> B) (x : A): Type
  := left_identity: forall y, op x y = y.
Class RightIdentity {A B} (op : A -> B -> A) (y : B): Type
  := right_identity: forall x, op x y = x.

Class Absorption {A B C} (op1: A -> C -> A) (op2: A -> B -> C) : Type
  := absorption: forall x y, op1 x (op2 x y) = x.

Class LeftAbsorb {A B} (op : A -> B -> A) (x : A): Type
  := left_absorb: forall y, op x y = x.
Class RightAbsorb {A B} (op : A -> B -> B) (y : B): Type
  := right_absorb: forall x, op x y = y.

Class LeftInverse {A} {B} {C} (op : A -> B -> C) (inv : B -> A) (unit : C)
  := left_inverse: forall x, op (inv x) x = unit.
Class RightInverse {A} {B} {C} (op : A -> B -> C) (inv : A -> B) (unit : C)
  := right_inverse: forall x, op x (inv x) = unit.

Class Commutative {B A} (f : A -> A -> B) : Type
  := commutativity: forall x y, f x y = f y x.

Class HeteroAssociative {A B C AB BC ABC}
  (fA_BC: A -> BC -> ABC) (fBC: B -> C -> BC)
  (fAB_C: AB -> C -> ABC) (fAB : A -> B -> AB): Type
  := associativity : forall x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative {A} (f : A -> A -> A)
  := simple_associativity :> HeteroAssociative f f f f.

Class Involutive {A} (f : A -> A) := involutive: forall x, f (f x) = x.

Class TotalRelation `(R : relation A) : Type := total : forall x y : A, R x y |_| R y x.
Arguments total {A} _ {TotalRelation} _ _.

Class Trichotomy `(R : relation A)
  := trichotomy : forall x y : A, R x y |_| x = y |_| R y x.
Arguments trichotomy {A} R {Trichotomy} _ _.

Arguments irreflexivity {A} _ {Irreflexive} _ _.

Class CoTransitive `(R : relation A) : Type := cotransitive
  : forall x y, R x y -> forall z, hor (R x z) (R z y).
Arguments cotransitive {A R CoTransitive x y} _ _.

Class AntiSymmetric `(R : relation A) : Type
  := antisymmetry: forall x y, R x y -> R y x -> x = y.
Arguments antisymmetry {A} _ {AntiSymmetric} _ _ _ _.

Class Equivalence `(R : relation A) : Type :=
  { Equivalence_Reflexive :> Reflexive R ;
    Equivalence_Symmetric :> Symmetric R ;
    Equivalence_Transitive :> Transitive R }.


Class LeftHeteroDistribute {A B C}
  (f : A -> B -> C) (g_r : B -> B -> B) (g : C -> C -> C) : Type
  := distribute_l : forall a b c, f a (g_r b c) = g (f a b) (f a c).
Class RightHeteroDistribute {A B C}
  (f : A -> B -> C) (g_l : A -> A -> A) (g : C -> C -> C) : Type
  := distribute_r: forall a b c, f (g_l a b) c = g (f a c) (f b c).
Class LeftDistribute {A} (f g: A -> A -> A)
  := simple_distribute_l :> LeftHeteroDistribute f g g.
Class RightDistribute {A} (f g: A -> A -> A)
  := simple_distribute_r :> RightHeteroDistribute f g g.

Class HeteroSymmetric {A} {T : A -> A -> Type}
  (R : forall {x y}, T x y -> T y x -> Type) : Type
  := hetero_symmetric `(a : T x y) (b : T y x) : R a b -> R b a.

(* Although cancellation is the same as being injective, we want a proper
  name to refer to this commonly used property. *)
Section cancellation.
  Context `(op : A -> A -> A) (z : A).

  Class LeftCancellation := left_cancellation : forall x y, op z x = op z y -> x = y.
  Class RightCancellation := right_cancellation : forall x y, op x z = op y z -> x = y.

  Context {Aap : Apart A}.

  Class StrongLeftCancellation := strong_left_cancellation
    : forall x y, x ≶ y -> op z x ≶ op z y.
  Class StrongRightCancellation := strong_right_cancellation
    : forall x y, x ≶ y -> op x z ≶ op y z.
End cancellation.

(* Common names for properties that hold in N, Z, Q, ... *)
Class ZeroProduct A `{!Mult A} `{!Zero A} : Type
  := zero_product : forall x y, x * y = 0 -> x = 0 |_| y = 0.

Class ZeroDivisor {R} `{Zero R} `{Mult R} (x : R) : Type
  := zero_divisor : x <> 0 /\ exists y, y <> 0 /\ x * y = 0.

Class NoZeroDivisors R `{Zero R} `{Mult R} : Type
  := no_zero_divisors x : ~ZeroDivisor x.

Instance zero_product_no_zero_divisors `{ZeroProduct A}
  : NoZeroDivisors A.
Proof.
intros x [? [? [? E]]].
destruct (zero_product _ _ E); auto.
Qed.

(* A common induction principle for both the naturals and integers *)
Class Biinduction R `{Zero R} `{One R} `{Plus R} : Type
  := biinduction (P : R -> Type)
  : P 0 -> (forall n, P n <-> P (1 + n)) -> forall n, P n.


(** Additional operations **)
Class CutMinus A := cut_minus : A -> A -> A.
Infix "∸" := cut_minus (at level 50, left associativity) : mc_scope.
Notation "(∸)" := cut_minus (only parsing) : mc_scope.
Notation "( x ∸)" := (cut_minus x) (only parsing) : mc_scope.
Notation "(∸ y )" := (fun x => x ∸ y) (only parsing) : mc_scope.

Inductive comparison : Set := LT | EQ | GT.

Class Compare A := compare : A -> A -> comparison.
Infix "?=" := compare (at level 70, no associativity) : mc_scope.
Notation "(?=)" := compare (only parsing) : mc_scope.
Notation "( x ?=)" := (compare x) (only parsing) : mc_scope.
Notation "(?= y )" := (fun x => x ?= y) (only parsing) : mc_scope.

Class Eqb A := eqb : A -> A -> Bool.
Infix "=?" := eqb (at level 70, no associativity) : mc_scope.
Notation "(=?)" := eqb (only parsing) : mc_scope.
Notation "( x =?)" := (eqb x) (only parsing) : mc_scope.
Notation "(=? y )" := (fun x => x =? y) (only parsing) : mc_scope.

Class Ltb A := ltb : A -> A -> Bool.
Infix "<?" := ltb (at level 70, no associativity) : mc_scope.
Notation "(<?)" := ltb (only parsing) : mc_scope.
Notation "( x <?)" := (ltb x) (only parsing) : mc_scope.
Notation "(<? y )" := (fun x => x <? y) (only parsing) : mc_scope.

Class Leb A := leb : A -> A -> Bool.
Infix "<=?" := leb (at level 70, no associativity) : mc_scope.
Notation "(<=?)" := leb (only parsing) : mc_scope.
Notation "( x <=?)" := (leb x) (only parsing) : mc_scope.
Notation "(<=? y )" := (fun x => x <=? y) (only parsing) : mc_scope.

Class Return (M : Type -> Type) := ret : forall {A}, A -> M A.

Class Bind (M : Type -> Type) := bind : forall {A B}, M A -> (A -> M B) -> M B.

Class Enumerable@{i} (A : Type@{i}) :=
  { enumerator : nat -> A
  ; enumerator_issurj :>
    TrM.RSU.IsConnMap@{Uhuge Ularge i i Ularge} (trunc_S minus_two) enumerator }.
Arguments enumerator A {_} _.
Arguments enumerator_issurj A {_} _.

(*
  The following class is nice to parametrize instances by additional properties, for example:
  [forall z, PropHolds (z <> 0) -> LeftCancellation op z]
  This tool is very powerful as we can combine it with instances as:
  [forall x y, PropHolds (x <> 0) -> PropHolds (y <> 0) -> PropHolds (x * y <> 0)]
  Of course, one should be very careful not to make too many instances as that could
  easily lead to a blow-up of the search space (or worse, cycles).
*)
Class PropHolds (P : Type) := prop_holds: P.

Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.

Ltac solve_propholds :=
  match goal with
  | [ |- PropHolds (?P) ] => apply _
  | [ |- ?P ] => change (PropHolds P); apply _
  end.
