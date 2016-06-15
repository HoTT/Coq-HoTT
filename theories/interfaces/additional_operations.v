Require Import HoTTClasses.interfaces.abstract_algebra.

Class Pow A B := pow : A → B → A.
Infix "**" := pow (at level 30, right associativity) : mc_scope.
Notation "(.**.)" := pow (only parsing) : mc_scope.
Notation "( x **.)" := (pow x) (only parsing) : mc_scope.
Notation "(.** n )" := (λ x, x ^ n) (only parsing) : mc_scope.

Class NatPowSpec A B (pw : Pow A B) `{One A} `{Mult A} `{Zero B} `{One B} `{Plus B} := {
  nat_pow_0 : ∀ x, x ** 0 = 1 ;
  nat_pow_S : ∀ x n, x ** (1 + n) = x * x ** n
}.

Class IntPowSpec A B (pow : Pow A B)
                 `{Zero A} `{One A} `{Mult A}
                 `{Zero B} `{One B} `{Plus B} :=
{ int_pow_0 : ∀ x, x ** 0 = 1
; int_pow_base_0 : ∀ (n : B), n ≠ 0 → 0 ** n = 0
; int_pow_S : ∀ x n, x ≠ 0 → x ** (1 + n) = x * x ** n }.

Class ShiftL A B := shiftl: A → B → A.
Infix "≪" := shiftl (at level 33, left associativity) : mc_scope.
Notation "(≪)" := shiftl (only parsing) : mc_scope.
Notation "( x ≪)" := (shiftl x) (only parsing) : mc_scope.
Notation "(≪ n )" := (λ x, x ≪ n) (only parsing) : mc_scope.

Class ShiftLSpec A B (sl : ShiftL A B)
  `{One A} `{Plus A} `{Mult A}
  `{Zero B} `{One B} `{Plus B} := {
  shiftl_0 :> RightIdentity (≪) 0 ;
  shiftl_S : ∀ x n, x ≪ (1 + n) = 2 * x ≪ n
}.

Lemma shiftl_spec_from_nat_pow `{SemiRing A} `{SemiRing B}
  {pw} `{!NatPowSpec A B pw} (sl : ShiftL A B) :
  (∀ x n, x ≪ n = x * 2 ** n) → ShiftLSpec A B sl.
Proof.
intros spec. split.
- intro x. rewrite spec, nat_pow_0. now apply right_identity.
- intros x n. rewrite 2!spec. rewrite nat_pow_S.
  rewrite (associativity x 2 (2 ** n)),
          (commutativity x 2).
  symmetry. apply associativity.
Qed.

Lemma shiftl_spec_from_int_pow `{SemiRing A} `{!PropHolds ((2:A) ≠ 0)}
  `{SemiRing B} {ip} `{!IntPowSpec A B ip} (sl : ShiftL A B) :
  (∀ x n, x ≪ n = x * 2 ** n) → ShiftLSpec A B sl.
Proof.
intros spec. split.
- intro x. rewrite spec, int_pow_0. apply right_identity.
- intros x n. rewrite 2!spec. rewrite int_pow_S by solve_propholds.
  rewrite (associativity x 2 _), (commutativity x 2).
  symmetry;apply associativity.
Qed.

Class ShiftR A B := shiftr: A → B → A.
Infix "≫" := shiftr (at level 33, left associativity) : mc_scope.
Notation "(≫)" := shiftr (only parsing) : mc_scope.

Class ShiftRSpec A B (sl : ShiftR A B)
  `{One A} `{Plus A} `{Mult A}
  `{Zero B} `{One B} `{Plus B} := {
  shiftr_0 :> RightIdentity (≫) 0 ;
  shiftr_S : ∀ x n, x ≫ n = (2 * x ≫ (1 + n))%mc ∨ x ≫ n = (2 * x ≫ (1 + n) + 1)%mc
}.

Class DivEuclid A := div_euclid : A → A → A.
Class ModEuclid A := mod_euclid : A → A → A.
Infix "`div`" := div_euclid (at level 35) : mc_scope.
Notation "(`div`)" := div_euclid (only parsing) : mc_scope.
Notation "( x `div`)" := (div_euclid x) (only parsing) : mc_scope.
Notation "(`div` y )" := (λ x, x `div` y) (only parsing) : mc_scope.
Infix "`mod`" := mod_euclid (at level 40) : mc_scope.
Notation "(`mod` )" := mod_euclid (only parsing) : mc_scope.
Notation "( x `mod`)" := (mod_euclid x) (only parsing) : mc_scope.
Notation "(`mod` y )" := (λ x, x `mod` y) (only parsing) : mc_scope.

Class EuclidSpec A (d : DivEuclid A) (m : ModEuclid A)
  `{Le A} `{Lt A} `{Zero A} `{Plus A} `{Mult A} := {
  div_mod : ∀ x y, y ≠ 0 → x = y * x `div` y + x `mod` y ;
  mod_rem : ∀ x y, y ≠ 0 → 0 ≤ x `mod` y < y ∨ y < x `mod` y ≤ 0 ;
  div_0 : ∀ x, x `div` 0 = 0 ;
  mod_0 : ∀ x, x `mod` 0 = 0
}.

Class CutMinus A := cut_minus : A → A → A.
Infix "∸" := cut_minus (at level 50, left associativity) : mc_scope.
Notation "(∸)" := cut_minus (only parsing) : mc_scope.
Notation "( x ∸)" := (cut_minus x) (only parsing) : mc_scope.
Notation "(∸ y )" := (λ x, x ∸ y) (only parsing) : mc_scope.

Class CutMinusSpec A (cm : CutMinus A) `{Zero A} `{Plus A} `{Le A} := {
  cut_minus_le : ∀ x y, y ≤ x → x ∸ y + y = x ;
  cut_minus_0 : ∀ x y, x ≤ y → x ∸ y = 0
}.
