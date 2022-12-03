From Coq Require Init.Tactics.
Require Import HoTT.

Fail Check Type0 : Type0.
Check Susp nat : Type0.
Fail Check Susp Type0 : Type0.

Fail Check (fun (P : interval -> Type) (a : P Interval.zero) (b : P Interval.one)
                (p p' : seg # a = b)
            => idpath : interval_ind P a b p = interval_rect P a b p').

Local Open Scope nat_scope.
Fail Check Lift nat : Type0.
Check 1 : Lift nat.

Check lift'@{i j}.
Check lower'@{i j}.
Check isequiv_lift'@{i j}.

(** Check that [ispointed_susp] doesn't require just a [Set] *)
Check (fun A : Type => _ : IsPointed (Susp A)).
Check (@ispointed_susp Type).
Check (@ispointed_susp Set).

(** Check that nested sigma-type notation didn't get clobbered by surreal cuts *)
Check ({ l : Unit & { n : Unit & Unit }}).

(** Test 1 from issue #754 *)
Module Issue754_1.
  Inductive nat : Type1 :=
  | O : nat
  | S : nat -> nat.
  Fixpoint code_nat (m n : nat) {struct m} : DProp.DHProp :=
    match m with
      | O => match n with
               | O => DProp.True
               | S _ => DProp.False
             end
      | S m' => match n with
                  | O => DProp.False
                  | S n' => code_nat m' n'
                end
    end.

  Local Set Warnings Append "-notation-overridden".
  Notation "x =n y" := (code_nat x y) : nat_scope.
  Local Set Warnings Append "notation-overridden".
  Bind Scope nat_scope with nat.
  Axiom equiv_path_nat :
    forall n m : nat,
      Trunc.trunctype_type (DProp.dhprop_hprop (n =n m)) <~> n = m.

  Definition nat_discr `{Funext} {n: nat}: O <> S n.
  Proof.
    intro H'.
    equiv_induction (@equiv_path_nat O (S n)).
    assumption.
  Qed.
End Issue754_1.

Module Issue_1358.

  Axiom A@{i} : Type@{i}.

  Axiom foo@{i} : A@{i} <~> A@{i}.

  Definition bar@{i} : A@{i} <~> A@{i}.
  Proof.
    reflexivity.
  Defined.

  Definition bar'@{i} : A@{i} <~> A@{i}.
  Proof.
    exact equiv_idmap.
  Defined.

End Issue_1358.

Module Issue_973.

  Inductive vec (A : Type) : nat -> Type :=
  | nil : vec A 0
  | cons : forall n : nat, A -> vec A n -> vec A (S n).
(*   Arguments nil [A]. *)

  Definition hd (A : Type) (n : nat) (v : vec A (S n)) : A :=
  match v in (vec _ (S n)) return A with
  | cons _ h _ => h
  end.

End Issue_973.


Module PR_1382.
  (* Tests for discriminate tactic *)

  Goal O = S O -> Empty.
   discriminate 1.
  Qed.

  Goal forall H : O = S O, H = H.
   discriminate H.
  Qed.

  Goal O = S O -> Unit.
  intros H. discriminate H. Qed.
  Goal O = S O -> Unit.
  intros H. Ltac g x := discriminate x. g H. Qed.

  Goal (forall x y : nat, x = y -> x = S y) -> Unit.
  intros.
  try discriminate (H O) || exact tt.
  Qed.

  Goal (forall x y : nat, x = y -> x = S y) -> Unit.
  intros H. ediscriminate (H O). instantiate (1:=O). Abort.

  (* Check discriminate on types with local definitions *)

  Inductive A := B (T := Unit) (x y : Bool) (z := x).
  Goal forall x y, B x true = B y false -> Empty.
  discriminate.
  Qed.

End PR_1382.


Require Import WildCat.SetoidRewrite.
Section SetoidRewriteTests.
  Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
      a $== b -> b $== c -> a $== c.
  Proof.
    intros A ? ? ? a b c eq_ab eq_bc.
    rewrite eq_ab, <- eq_bc.
  Abort.
  Goal forall (A : Type) `(H : Is0Gpd A) (a b c : A),
      a $== b -> b $== c -> a $== c.
  Proof.
    intros A ? ? ? a b c eq_ab eq_bc.
    symmetry.
    rewrite eq_ab, <- eq_bc.
    rewrite eq_bc.
    rewrite <- eq_bc.
  Abort.

  Goal forall (A B : Type) (F : A -> B) `{Is1Functor _ _ F} (a b : A) (f g : a $-> b), f $== g -> fmap F f $== fmap F g.
  Proof.
    do 17 intro.
    intro eq_fg.
    rewrite eq_fg.
  Abort.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g : b $-> c), f1 $== f2 -> g $o f1 $== g $o f2.
  Proof.
    do 11 intro.
    intro eq.
    rewrite <- eq.
    rewrite eq.
  Abort.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> g1 $o f $== g2 $o f.
  Proof.
  do 11 intro.
  intro eq.
  rewrite <- eq.
  rewrite eq.
  rewrite <- eq.
  Abort.

  Goal forall (A : Type) `{Is1Cat A} (a b c : A) (f1 f2 : a $-> b) (g1 g2 : b $-> c), g1 $== g2 -> f1 $== f2 -> g1 $o f1 $== g2 $o f2.
  Proof.
    do 12 intro.
    intros eq_g eq_f.
    rewrite eq_g.
    rewrite <- eq_f.
    rewrite eq_f.
    rewrite <- eq_g.
  Abort.
End SetoidRewriteTests.
