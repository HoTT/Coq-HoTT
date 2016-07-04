Require Import
  HoTTClasses.interfaces.canonical_names.

Definition ap2 `(f : A -> B -> C) {x1 x2 y1 y2}:
  x1 = x2 -> y1 = y2 -> f x1 y1 = f x2 y2.
Proof.
intros H1 H2;destruct H1,H2;reflexivity.
Defined.

Section pointwise_dependent_relation.
  Context A (B: A → Type) (R: ∀ a, relation (B a)).

  Definition pointwise_dependent_relation: relation (∀ a, B a) :=
    λ f f', ∀ a, R _ (f a) (f' a).

  Global Instance pdr_equiv {_:∀ a, Equivalence (R a)}
    : Equivalence pointwise_dependent_relation.
  Proof.
  split.
  - intros f a.
    apply reflexivity.
  - intros f g H a.
    apply symmetry;auto.
  - intros f g h H1 H2 a.
    transitivity (g a);auto.
  Qed.
End pointwise_dependent_relation.

Definition iffT (A B: Type): Type := prod (A → B) (B → A).

(* Class NonEmpty (A : Type) : Type := non_empty : inhabited A. *)
Class NonEmptyT (A : Type) : Type := non_emptyT : A.

Definition uncurry {A B C} (f: A → B → C) (p: A * B): C := f (fst p) (snd p).

Definition is_sole {T} (P: T → Type) (x: T) : Type := P x ∧ ∀ y, P y → y = x.

Definition DN (T: Type): Type := (T → False) → False.
Class Stable P := stable: DN P → P.
(* TODO: include useful things from corn/logic/Stability.v
   and move to separate file *)

Class Obvious (T : Type) := obvious: T.

Section obvious.
  Context (A B C: Type).

  Global Instance: Obvious (A → A) := id.
  Global Instance: Obvious (False → A) := Empty_rect _.
  Global Instance: Obvious (A → A + B)%type := inl.
  Global Instance: Obvious (A → B + A)%type := inr.
  Global Instance obvious_sum_src `{Obvious (A → C)} `{Obvious (B → C)}
    : Obvious (A+B → C)%type.
  Proof.
    intros [?|?]; auto.
  Defined.

  Global Instance obvious_sum_dst_l `{Obvious (A → B)}
    : Obvious (A → B+C)%type.
  Proof.
    red;auto.
  Defined.

  Global Instance obvious_sum_dst_r `{Obvious (A → B)}: Obvious (A → C\/B).
  Proof.
    red;auto.
  Defined.
End obvious.

Lemma not_symmetry `{Symmetric A R} (x y: A): ¬R x y → ¬R y x.
Proof.
auto.
Qed.
(* Also see Coq bug #2358.
   A totally different approach would be to define negated relations
   such as inequality as separate relations rather than notations,
   so that the existing [symmetry] will work for them.
   However, this most likely breaks other things. *)

Lemma iff_true : forall P, P -> True <-> P.
Proof.
intros P p;split;auto.
Defined.

Lemma iff_false : forall P, ¬ P -> False <-> P.
Proof.
intros P n;split.
- apply obvious.
- exact n.
Defined.

Lemma biinduction_iff `{Biinduction R}
  (P1 : Type) (P2 : R → Type) :
  (P1 ↔ P2 0) → (∀ n, P2 n ↔ P2 (1 + n)) → ∀ n, P1 ↔ P2 n.
Proof.
intros init ind.
apply biinduction.
- assumption.
- intros n. split.
  + intros X.
    apply (transitivity X).
    apply ind.
  + intros X.
    apply (transitivity X).
    apply symmetry. apply ind.
Qed.

(* Isn't this in the stdlib? *)
Definition is_Some `(x : option A) :=
  match x with
  | None => False
  | Some _ => True
  end.

Lemma is_Some_def `(x : option A) :
  is_Some x ↔ ∃ y, x = Some y.
Proof.
unfold is_Some.
destruct x.
- apply iff_true. exists a;reflexivity.
- apply iff_false. intros [y H].
  change (@is_Some A None).
  apply transport with (Some y).
  + Symmetry. assumption.
  + simpl. auto.
Qed.

Definition is_None `(x : option A) :=
  match x with
  | None => True
  | Some _ => False
  end.

Lemma is_None_def `(x : option A) :
  is_None x ↔ x = None.
Proof.
unfold is_None. destruct x as [a|].
- apply iff_false.
  intros H.
  change (is_None (Some a)).
  apply transport with None.
  + Symmetry;assumption.
  + simpl;auto.
- apply iff_true. reflexivity.
Qed.

Lemma None_ne_Some `(x : A) :
  ~ (None = Some x).
Proof.
intros e.
change (is_None (Some x)).
apply transport with None.
- assumption.
- simpl;auto.
Qed.

Fixpoint repeat {A:Type} (n:nat) (f : A -> A) (x : A) : A :=
  match n with
  | 0 => x
  | S k => f (repeat k f x)
  end.
