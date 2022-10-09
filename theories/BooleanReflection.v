From HoTT Require Import Basics
  Types.Bool
  Types.Sum
  Basics.Utf8
  Basics.Tactics 
  Basics.Decidable
  Classes.interfaces.abstract_algebra.

#[export] Instance negb_involutive : Involutive negb. 
Proof.
  intro a; destruct a; reflexivity.
Defined.

#[export] Instance orb_comm : Commutative orb. 
Proof.
  intros a b; destruct a, b; done.
Defined.

#[export] Instance orb_assoc : Associative orb. 
Proof.
  intros a b c. destruct a; reflexivity.
Defined.

#[export] Instance andb_assoc : Associative andb. 
Proof.
  intros a b c. destruct a; reflexivity.
Defined.

#[export] Instance andb_comm : Commutative andb. 
Proof.
  intros a b. destruct a, b; reflexivity.
Defined.

Definition is_true (b : Bool) := b = true.

Coercion is_true : Bool >-> Sortclass.

Variant reflect (P : Type) : Bool -> Type :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Proposition rwP {P : Type} {b : Bool} (p : reflect P b) : P <-> b.
Proof.
  split; destruct p; try discriminate; done.
Defined.

Proposition iffP (P : Type) (b : Bool) (p : P -> b) (q : b -> P) : reflect P b.
Proof.
  destruct b.
  - constructor; by apply q.
  - constructor; intro a; apply p in a; discriminate.
Defined.

Definition decBool (A : Type) `{Decidable A} : Bool :=
  match dec A with
  | inl _ => true
  | inr _ => false
  end.

Proposition decP (A : Type) `{Decidable A} : reflect A (decBool A).
Proof.
  unfold decBool; destruct dec; constructor; assumption.
Defined.

Proposition decBoolSum (A B: Type) `{H0 : Decidable A} `{H1 : Decidable B} :
  decBool (A + B) = orb (decBool A) (decBool B).
Proof.
  unfold decBool.
  unfold dec, decidable_sum at 1, dec. destruct H0, H1; done.
Defined.

Global Instance neg_dec {A : Type} {P : Decidable A} : Decidable (~ A).
Proof.
  case P.
  - intro a. right. intro contr; contradiction contr.
  - intro na. now left.
Defined.

Proposition decBoolNegb (A : Type) `{H0 : Decidable A} :
  decBool (~ A) = negb (decBool A).
Proof.
  unfold decBool.
  unfold neg_dec, dec.
  by destruct H0.
Defined.    

Proposition not_true_iff_false (b : Bool) : (~ b) <-> b = false.
Proof.
  destruct b; split.
  - intro H; by contradiction H.
  - intro H; discriminate.
  - reflexivity.
  - discriminate.
Defined.

Proposition andP (a b : Bool) : reflect (a * b) (a && b).
Proof.
  apply iffP.
  - intro H; destruct H as [ar br].
    unfold is_true in ar; symmetry in ar; destruct ar.
    unfold is_true in br; symmetry in br; destruct br.
    reflexivity.
  - destruct a, b; try discriminate; done.
Defined.

Proposition orP (a b : Bool) : reflect (a + b) (a || b).
Proof.
  apply iffP.
  - intro H; destruct H as [atrue | btrue].
    + unfold is_true in atrue; symmetry in atrue; destruct atrue; reflexivity.
    + unfold is_true in btrue; symmetry in btrue; destruct btrue.
      destruct (symmetry _ _ (@commutativity Bool Bool orb _ a true)); reflexivity.
  - destruct a.
    + intros _. left; reflexivity.
    + simpl; intro t; right; assumption.
Defined.

Proposition elimN {P : Type} {b : Bool} (p : reflect P b)  : negb b -> ~P. 
Proof.
  destruct p; [ discriminate | done ].
Defined.

Lemma introN {P : Type} {b : Bool} (p : reflect P b) : ~ P -> negb b.
Proof.
  intro np.
  destruct p ; [ by contradiction np | reflexivity ].
Defined.
