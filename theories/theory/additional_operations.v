Require Import HoTTClasses.interfaces.abstract_algebra.

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


Lemma LT_EQ : ~ LT = EQ.
Proof.
intros E.
change ((fun r => match r with LT => Unit | _ => Empty end) EQ).
transport E. split.
Qed.

Lemma LT_GT : ~ LT = GT.
Proof.
intros E.
change ((fun r => match r with LT => Unit | _ => Empty end) GT).
transport E. split.
Qed.

Lemma EQ_LT : ~ EQ = LT.
Proof.
apply symmetric_neq, LT_EQ.
Qed.

Lemma EQ_GT : ~ EQ = GT.
Proof.
intros E.
change ((fun r => match r with EQ => Unit | _ => Empty end) GT).
transport E. split.
Qed.

Lemma GT_EQ : ~ GT = EQ.
Proof.
apply symmetric_neq, EQ_GT.
Qed.
