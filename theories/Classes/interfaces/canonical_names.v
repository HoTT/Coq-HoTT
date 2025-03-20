Require Export
  HoTT.Basics
  HoTT.Types
  HoTT.Truncations.Core.

Declare Scope mc_scope.

Open Scope mc_scope.

Generalizable Variables A B f g x y.

Monomorphic Universe Ularge Uhuge.
Monomorphic Constraint Ularge < Uhuge.

Lemma merely_destruct {A} {P : Type} {sP : IsHProp P}
  (x : merely A) : (A -> P) -> P.
Proof.
intros E;revert x.
apply Trunc_ind.
- exact _.
- exact E.
Qed.

Notation " g ∘ f " := (Compose g f).
Notation "(∘)" := Compose (only parsing) : mc_scope.

Definition id {A : Type} (a : A) := a.

Notation "(=)" := paths (only parsing) : mc_scope.
Notation "( x =)" := (paths x) (only parsing) : mc_scope.
Notation "(= x )" := (fun y => paths y x) (only parsing) : mc_scope.

Notation "(<>)" := (fun x y => ~x = y) (only parsing) : mc_scope.
Notation "( x <>)" := (fun y => x <> y) (only parsing) : mc_scope.
Notation "(<> x )" := (fun y => y <> x) (only parsing) : mc_scope.

Class Apart A := apart : Relation A.
Infix "≶" := apart : mc_scope.
Notation "(≶)" := apart (only parsing) : mc_scope.
Notation "( x ≶)" := (apart x) (only parsing) : mc_scope.
Notation "(≶ x )" := (fun y => apart y x) (only parsing) : mc_scope.

(* Even for setoids with decidable equality x <> y does not imply x ≶ y.
Therefore we introduce the following class. *)
Class TrivialApart A {Aap : Apart A} :=
  { trivial_apart_prop :: is_mere_relation A apart
  ; trivial_apart : forall x y, x ≶ y <-> x <> y }.

Definition sig_apart `{Apart A} (P: A -> Type) : Apart (sig P) := fun x y => x.1 ≶ y.1.
#[export]
Hint Extern 10 (Apart (sig _)) => apply @sig_apart : typeclass_instances.

Class Cast A B := cast: A -> B.
Arguments cast _ _ {Cast} _.
Notation "' x" := (cast _ _ x) : mc_scope.
#[global] Typeclasses Transparent Cast.

(* Other canonically named relations/operations/constants: *)
Class SgOp A := sg_op: A -> A -> A.
Class MonUnit A := mon_unit: A.
Class Plus A := plus: A -> A -> A.
Class Mult A := mult: A -> A -> A.
Class One A := one: A.
Class Zero A := zero: A.
Class Negate A := negate: A -> A.
Class Inverse A := inv: A -> A.
Class DecRecip A := dec_recip: A -> A.
Definition ApartZero R `{Zero R} `{Apart R} := sig (≶ zero).
Class Recip A `{Apart A} `{Zero A} := recip: ApartZero A -> A.
#[global] Typeclasses Transparent SgOp MonUnit Plus Mult Zero One Negate.

Class Meet A := meet: A -> A -> A.
Class Join A := join: A -> A -> A.
Class Top A := top: A.
Class Bottom A := bottom: A.
#[global] Typeclasses Transparent Meet Join Top Bottom.

Class Le A := le: Relation A.
Class Lt A := lt: Relation A.
#[global] Typeclasses Transparent Le Lt.

Definition NonNeg R `{Zero R} `{Le R} := sig (le zero).
Definition Pos R `{Zero R} `{Lt R} := sig (lt zero).
Definition NonPos R `{Zero R} `{Le R} := sig (fun y => le y zero).

(** *** Hints for converting between types of operations *)

Instance plus_is_sg_op `{f : Plus A} : SgOp A := f.
Definition sg_op_is_plus `{f : SgOp A} : Plus A := f.

Instance mult_is_sg_op `{f : Mult A} : SgOp A := f.
Definition sg_op_is_mult `{f : SgOp A} : Mult A := f.

Instance zero_is_mon_unit `{c : Zero A} : MonUnit A := c.
Definition mon_unit_is_zero `{c : MonUnit A} : Zero A := c.

Instance one_is_mon_unit `{c : One A} : MonUnit A := c.
Definition mon_unit_is_one `{c : MonUnit A} : One A := c.

Instance meet_is_sg_op `{f : Meet A} : SgOp A := f.

Instance join_is_sg_op `{f : Join A} : SgOp A := f.

Definition top_is_mon_unit `{s : Top A} : MonUnit A := s.

Definition bottom_is_mon_unit `{s : Bottom A} : MonUnit A := s.

Instance negate_is_inverse `{i : Negate A} : Inverse A := i.
Definition inverse_is_negate `{i : Inverse A} : Negate A := i.

#[export]
Hint Extern 4 (Apart (ApartZero _)) => apply @sig_apart : typeclass_instances.
#[export]
Hint Extern 4 (Apart (NonNeg _)) => apply @sig_apart : typeclass_instances.
#[export]
Hint Extern 4 (Apart (Pos _)) => apply @sig_apart : typeclass_instances.

(** For more information on using [mc_add_scope] and [mc_mult_scope], see the files test/Algebra/Groups/Expressions.v and test/Algebra/Rings/Expressions.v. *)

Module AdditiveNotations.

  (** [mc_add_scope] is generally used when working with abelian groups. *)

  Declare Scope mc_add_scope.
  Infix "+" := sg_op : mc_add_scope.
  Notation "(+)" := sg_op (only parsing) : mc_add_scope.
  Notation "( x +)" := (sg_op x) (only parsing) : mc_add_scope.
  Notation "(+ x )" := (fun y => sg_op y x) (only parsing) : mc_add_scope.
  
  Notation "0" := mon_unit : mc_add_scope.

  Notation "- x" := (inv x) : mc_add_scope.
  Notation "(-)" := inv (only parsing) : mc_add_scope.
  Notation "x - y" := (sg_op x (inv y)) : mc_add_scope.

End AdditiveNotations.

Module MultiplicativeNotations.

  (** [mc_mult_scope] is generally used when working with general groups. *)

  Declare Scope mc_mult_scope.
  Infix "*" := sg_op : mc_mult_scope.
  Notation "( x *.)" := (sg_op x) (only parsing) : mc_mult_scope.
  Notation "(.*.)" := sg_op (only parsing) : mc_mult_scope.
  Notation "(.* x )" := (fun y => sg_op y x) (only parsing) : mc_mult_scope.

  Notation "1" := mon_unit : mc_mult_scope.

  Notation "x ^" := (inv x) : mc_mult_scope.
  Notation "(^)" := inv (only parsing) : mc_mult_scope.

End MultiplicativeNotations.

(** We group these notations into a module, so that just this subset can be exported in some cases. *)
Module Export BinOpNotations.
  Export AdditiveNotations MultiplicativeNotations.

  Infix "+" := plus : mc_scope.
  Notation "(+)" := plus (only parsing) : mc_scope.
  Notation "( x +)" := (plus x) (only parsing) : mc_scope.
  Notation "(+ x )" := (fun y => y + x) (only parsing) : mc_scope.

  Infix "*" := mult : mc_scope.
  (* We don't add "( * )", "( * x )" and "( x * )" notations because they conflict with comments. *)
  Notation "( x *.)" := (mult x) (only parsing) : mc_scope.
  Notation "(.*.)" := mult (only parsing) : mc_scope.
  Notation "(.* x )" := (fun y => y * x) (only parsing) : mc_scope.

  Notation "- x" := (negate x) : mc_scope.
  Notation "(-)" := negate (only parsing) : mc_scope.
  Notation "x - y" := (x + negate y) : mc_scope.

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
End BinOpNotations.

Notation "/ x" := (dec_recip x) : mc_scope.
Notation "(/)" := dec_recip (only parsing) : mc_scope.
Notation "x / y" := (x * /y) : mc_scope.

Notation "// x" := (recip x) : mc_scope.
Notation "(//)" := recip (only parsing) : mc_scope.
Notation "x // y" := (x * //y) : mc_scope.

Notation "⊤" := top : mc_scope.
Notation "⊥" := bottom : mc_scope.

Infix "⊓" := meet : mc_scope.
Notation "(⊓)" := meet (only parsing) : mc_scope.
Notation "( X ⊓)" := (meet X) (only parsing) : mc_scope.
Notation "(⊓ X )" := (fun Y => Y ⊓ X) (only parsing) : mc_scope.

Infix "⊔" := join : mc_scope.
Notation "(⊔)" := join (only parsing) : mc_scope.
Notation "( X ⊔)" := (join X) (only parsing) : mc_scope.
Notation "(⊔ X )" := (fun Y => Y ⊔ X) (only parsing) : mc_scope.

Infix "≤" := le : mc_scope.
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

Notation "x ≤ y ≤ z" := (x ≤ y /\ y ≤ z) : mc_scope.
Notation "x ≤ y < z" := (x ≤ y /\ y < z) : mc_scope.
Notation "x < y < z" := (x < y /\ y < z) : mc_scope.
Notation "x < y ≤ z" := (x < y /\ y ≤ z) : mc_scope.

(** It is likely that ≤ and < are transitive (and ≤ reflexive) so inform [auto] of this. *)
Ltac auto_trans := match goal with
                    [ H: ?R ?x ?y, I: ?R ?y ?z |- ?R ?x ?z] => apply (transitivity H I)
                  end.

#[export]
Hint Extern 2 (?x ≤ ?y) => reflexivity : core.
#[export]
Hint Extern 4 (?x ≤ ?z) => auto_trans : core.
#[export]
Hint Extern 4 (?x < ?z) => auto_trans : core.

Class Abs A `{Le A} `{Zero A} `{Negate A}
  := abs_sig: forall (x : A), { y : A | (0 ≤ x -> y = x) /\ (x ≤ 0 -> y = -x)}.
Definition abs `{Abs A} := fun x : A => (abs_sig x).1.

(* Common properties: *)
(* Class Inverse `(A -> B) : Type := inverse: B -> A.
Arguments inverse {A B} _ {Inverse} _.
Typeclasses Transparent Inverse.
Notation "f ⁻¹" := (inverse f) : mc_scope. *)

Class Idempotent `(f: A -> A -> A) (x : A) : Type := idempotency: f x x = x.
Arguments idempotency {A} _ _ {Idempotent}.

Class UnaryIdempotent {A} (f: A -> A) : Type :=
  unary_idempotent :: Idempotent Compose f.

Lemma unary_idempotency `{UnaryIdempotent A f} x : f (f x) = f x.
Proof.
change (f (f x)) with (Compose f f x).
apply (ap (fun g => g x)).
change (Compose f f = f).
apply idempotency. exact _.
Qed.

Class BinaryIdempotent `(op: A -> A -> A) : Type
  := binary_idempotent :: forall x, Idempotent op x.

Class LeftIdentity {A B} (op : A -> B -> B) (x : A): Type
  := left_identity: forall y, op x y = y.

Instance istrunc_leftidentity `{Funext} {n A B} op x
   : IsTrunc n.+1 B -> IsTrunc n (@LeftIdentity A B op x).
Proof.
  unfold LeftIdentity; exact _.
Defined.

Class RightIdentity {A B} (op : A -> B -> A) (y : B): Type
  := right_identity: forall x, op x y = x.

Instance istrunc_rightidentity `{Funext} {n A B} op y
  : IsTrunc n.+1 A -> IsTrunc n (@RightIdentity A B op y).
Proof.
  unfold RightIdentity; exact _.
Defined.

Class Absorption {A B C} (op1: A -> C -> A) (op2: A -> B -> C) : Type
  := absorption: forall x y, op1 x (op2 x y) = x.

Class LeftAbsorb {A B} (op : A -> B -> A) (x : A): Type
  := left_absorb: forall y, op x y = x.
Class RightAbsorb {A B} (op : A -> B -> B) (y : B): Type
  := right_absorb: forall x, op x y = y.

Class LeftInverse {A} {B} {C} (op : A -> B -> C) (inv : B -> A) (unit : C)
  := left_inverse: forall x, op (inv x) x = unit.

Instance istrunc_leftinverse `{Funext} {n A B C} op inv unit
  : IsTrunc n.+1 C -> IsTrunc n (@LeftInverse A B C op inv unit).
Proof.
  unfold LeftInverse; exact _.
Defined.

Class RightInverse {A} {B} {C} (op : A -> B -> C) (inv : A -> B) (unit : C)
  := right_inverse: forall x, op x (inv x) = unit.

Instance istrunc_rightinverse `{Funext} {n A B C} op inv unit
  : IsTrunc n.+1 C -> IsTrunc n (@RightInverse A B C op inv unit).
Proof.
  unfold RightInverse; exact _.
Defined.

Class Commutative {B A} (f : A -> A -> B) : Type
  := commutativity: forall x y, f x y = f y x.

#[global] Typeclasses Transparent Commutative.

Class HeteroAssociative {A B C AB BC ABC}
  (fA_BC: A -> BC -> ABC) (fBC: B -> C -> BC)
  (fAB_C: AB -> C -> ABC) (fAB : A -> B -> AB): Type
  := associativity : forall x y z, fA_BC x (fBC y z) = fAB_C (fAB x y) z.
Class Associative {A} (f : A -> A -> A)
  := simple_associativity :: HeteroAssociative f f f f.

Instance istrunc_associative `{Funext} A n f `{IsTrunc n.+1 A}
  : IsTrunc n (@Associative A f).
Proof.
  unfold Associative, HeteroAssociative; exact _.
Defined.

Definition associative_flip A f
  : @Associative A f -> Associative (flip f).
Proof.
  intros assoc z y x; unfold flip.
  exact (assoc x y z)^.
Defined.
Hint Immediate associative_flip : typeclass_instances.

Class Involutive {A} (f : A -> A) := involutive: forall x, f (f x) = x.

Class TotalRelation `(R : Relation A) : Type := total : forall x y : A, R x y |_| R y x.
Arguments total {A} _ {TotalRelation} _ _.

Class Trichotomy `(R : Relation A)
  := trichotomy : forall x y : A, R x y |_| x = y |_| R y x.
Arguments trichotomy {A} R {Trichotomy} _ _.

Arguments irreflexivity {A} _ {Irreflexive} _ _.

Class CoTransitive `(R : Relation A) : Type := cotransitive
  : forall x y, R x y -> forall z, hor (R x z) (R z y).
Arguments cotransitive {A R CoTransitive x y} _ _.

Class EquivRel `(R : Relation A) : Type := Build_EquivRel
  { EquivRel_Reflexive :: Reflexive R ;
    EquivRel_Symmetric :: Symmetric R ;
    EquivRel_Transitive :: Transitive R }.

Definition SigEquivRel {A:Type} (R : Relation A) : Type :=
  {_ : Reflexive R | { _ : Symmetric R | Transitive R}}.

Instance trunc_sig_equiv_rel `{Funext} {A : Type}
  (R : Relation A) {n} `{!forall (x y : A), IsTrunc n (R x y)}
  :  IsTrunc n (SigEquivRel R).
Proof.
  apply @istrunc_sigma.
  - exact istrunc_forall.
  - intros. apply @istrunc_sigma; intros; exact istrunc_forall.
Defined.

Lemma issig_equiv_rel {A:Type} (R : Relation A)
  : SigEquivRel R <~> EquivRel R.
Proof.
  issig.
Defined.

Instance istrunc_equiv_rel `{Funext} {A : Type}
  (R : Relation A) {n} `{!forall (x y : A), IsTrunc n (R x y)}
  : IsTrunc n (EquivRel R).
Proof.
  exact (istrunc_equiv_istrunc (SigEquivRel R) (issig_equiv_rel R)).
Qed.

Class Conjugate A := conj : A -> A.

Class DistrOpp {A} `(SgOp A) `(Conjugate A)
  := distropp : forall x y : A, conj (sg_op x y) = sg_op (conj y) (conj x).

Class SwapOp {A} `(Negate A) `(Conjugate A)
  := swapop : forall x, conj (-x) = - (conj x).

Class FactorNegLeft {A} `(Negate A) `(SgOp A)
  := factorneg_l : forall x y, sg_op (-x) y = - (sg_op x y).

Class FactorNegRight {A} `(Negate A) `(SgOp A)
  := factorneg_r : forall x y, sg_op x (-y) = - (sg_op x y).

Class LeftHeteroDistribute {A B C}
  (f : A -> B -> C) (g_r : B -> B -> B) (g : C -> C -> C) : Type
  := distribute_l : forall a b c, f a (g_r b c) = g (f a b) (f a c).
Class RightHeteroDistribute {A B C}
  (f : A -> B -> C) (g_l : A -> A -> A) (g : C -> C -> C) : Type
  := distribute_r: forall a b c, f (g_l a b) c = g (f a c) (f b c).
Class LeftDistribute {A} (f g: A -> A -> A)
  := simple_distribute_l :: LeftHeteroDistribute f g g.

Class RightDistribute {A} (f g: A -> A -> A)
  := simple_distribute_r :: RightHeteroDistribute f g g.

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
Infix "∸" := cut_minus : mc_scope.
Notation "(∸)" := cut_minus (only parsing) : mc_scope.
Notation "( x ∸)" := (cut_minus x) (only parsing) : mc_scope.
Notation "(∸ y )" := (fun x => x ∸ y) (only parsing) : mc_scope.

Inductive comparison : Set := LT | EQ | GT.

Class Compare A := compare : A -> A -> comparison.
Infix "?=" := compare : mc_scope.
Notation "(?=)" := compare (only parsing) : mc_scope.
Notation "( x ?=)" := (compare x) (only parsing) : mc_scope.
Notation "(?= y )" := (fun x => x ?= y) (only parsing) : mc_scope.

Class Eqb A := eqb : A -> A -> Bool.
Infix "=?" := eqb : mc_scope.
Notation "(=?)" := eqb (only parsing) : mc_scope.
Notation "( x =?)" := (eqb x) (only parsing) : mc_scope.
Notation "(=? y )" := (fun x => x =? y) (only parsing) : mc_scope.

Class Ltb A := ltb : A -> A -> Bool.
Infix "<?" := ltb : mc_scope.
Notation "(<?)" := ltb (only parsing) : mc_scope.
Notation "( x <?)" := (ltb x) (only parsing) : mc_scope.
Notation "(<? y )" := (fun x => x <? y) (only parsing) : mc_scope.

Class Leb A := leb : A -> A -> Bool.
Infix "<=?" := leb : mc_scope.
Notation "(<=?)" := leb (only parsing) : mc_scope.
Notation "( x <=?)" := (leb x) (only parsing) : mc_scope.
Notation "(<=? y )" := (fun x => x <=? y) (only parsing) : mc_scope.

Class Return (M : Type -> Type) := ret : forall {A}, A -> M A.

Class Bind (M : Type -> Type) := bind : forall {A B}, M A -> (A -> M B) -> M B.

Class Enumerable@{i} (A : Type@{i}) :=
  { enumerator : nat -> A
  ; enumerator_issurj :: IsSurjection enumerator }.

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

#[export]
Hint Extern 0 (PropHolds _) => assumption : typeclass_instances.

Ltac solve_propholds :=
  match goal with
  | [ |- PropHolds (?P) ] => apply _
  | [ |- ?P ] => change (PropHolds P); apply _
  end.
