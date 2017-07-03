Require Import HoTTClasses.interfaces.abstract_algebra.

Local Set Universe Minimization ToSet.

Lemma shiftl_spec_from_nat_pow `{SemiRing A} `{SemiRing B}
  {pw} `{!NatPowSpec A B pw} (sl : ShiftL A B) :
  (forall x n, x ≪ n = x * 2 ^^ n) -> ShiftLSpec A B sl.
Proof.
intros spec. split.
- intro x. rewrite spec, nat_pow_0. now apply right_identity.
- intros x n. rewrite 2!spec. rewrite nat_pow_S.
  rewrite (associativity x 2 (2 ^^ n)),
          (commutativity x 2).
  symmetry. apply associativity.
Qed.

Lemma shiftl_spec_from_int_pow `{SemiRing A} `{!PropHolds ((2:A) <> 0)}
  `{SemiRing B} {ip} `{!IntPowSpec A B ip} (sl : ShiftL A B) :
  (forall x n, x ≪ n = x * 2 ^^ n) -> ShiftLSpec A B sl.
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
rewrite <-E. split.
Qed.

Lemma LT_GT : ~ LT = GT.
Proof.
intros E.
change ((fun r => match r with LT => Unit | _ => Empty end) GT).
rewrite <-E. split.
Qed.

Lemma EQ_LT : ~ EQ = LT.
Proof.
apply symmetric_neq, LT_EQ.
Qed.

Lemma EQ_GT : ~ EQ = GT.
Proof.
intros E.
change ((fun r => match r with EQ => Unit | _ => Empty end) GT).
rewrite <-E. split.
Qed.

Lemma GT_EQ : ~ GT = EQ.
Proof.
apply symmetric_neq, EQ_GT.
Qed.

Instance compare_eqb `{Compare A} : Eqb A | 2 := fun a b =>
  match a ?= b with
  | EQ => true
  | _ => false
  end.

Lemma compare_eqb_eq `{Compare A} : forall a b : A, a =? b = true -> a ?= b = EQ.
Proof.
unfold eqb,compare_eqb;simpl.
intros a b. destruct (a ?= b);trivial;intros E;destruct (false_ne_true E).
Qed.

Instance tricho_compare `{Trichotomy A R} : Compare A | 2
  := fun a b =>
  match trichotomy R a b with
  | inl _ => LT
  | inr (inl _) => EQ
  | inr (inr _) => GT
  end.

Lemma tricho_compare_eq `{Trichotomy A R}
  : forall a b : A, compare a b = EQ -> a = b.
Proof.
unfold compare,tricho_compare.
intros a b;destruct (trichotomy R a b) as [E|[E|E]];auto.
- intros E1;destruct (LT_EQ E1).
- intros E1;destruct (GT_EQ E1).
Qed.

Lemma tricho_compare_ok `{Trichotomy A R} `{Irreflexive A R}
  : forall a b : A, compare a b = EQ <-> a = b.
Proof.
unfold compare,tricho_compare.
intros a b;destruct (trichotomy R a b) as [E1|[E1|E1]];split;auto.
- intros E2;destruct (LT_EQ E2).
- intros E2;rewrite E2 in E1. destruct (irreflexivity R _ E1).
- intros E2;destruct (GT_EQ E2).
- intros E2;rewrite E2 in E1. destruct (irreflexivity R _ E1).
Qed.

Lemma total_abs_either `{Abs A} `{!TotalRelation le}
  : forall x : A, (0 <= x /\ abs x = x) \/ (x <= 0 /\ abs x = - x).
Proof.
intros x.
destruct (total le 0 x) as [E|E].
- left. split;trivial. apply ((abs_sig x).2);trivial.
- right. split;trivial. apply ((abs_sig x).2);trivial.
Qed.

