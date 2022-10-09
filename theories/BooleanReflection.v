From HoTT Require Import Basics Types.Bool Types.Sum Basics.Utf8 Basics.Tactics 
  Basics.Decidable.

Variant reflect (P : Type) : Bool -> Type :=
  | ReflectT : P -> reflect P true
  | ReflectF : ~ P -> reflect P false.

Proposition iff_reflect (P : Type) (b : Bool) : (reflect P b) <-> (P <-> b = true).
  Proof.
    split.
    - intro r; destruct r.
      + split; done.
      + split; [ contradiction | discriminate ].
    - intro H; destruct H as [if1 if2].
      destruct b.
      + apply ReflectT, if2; reflexivity.
      + apply ReflectF; intro p; apply if1 in p; discriminate.
  Defined.

  Proposition refl_tofalse (A : Type) (b : Bool) (p : reflect A b) : ~ A -> b = false.
  Proof.
    destruct p; done.
  Defined.

  Proposition refl_totrue (A : Type) (b : Bool) (p : reflect A b) : A -> b = true.
  Proof.
    destruct p; done.
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
  Qed.

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
  Qed.    

  Proposition not_true_iff_false (b : Bool) : (b <> true) <-> b = false.
  Proof.
    destruct b; split.
    - intro H; by contradiction H.
    - intro H; discriminate.
    - reflexivity.
    - discriminate.
  Defined.

  Proposition orb_comm (a b : Bool) : (a || b)%Bool = (b || a)%Bool.
  Proof.
    destruct a, b; done.
  Defined.
