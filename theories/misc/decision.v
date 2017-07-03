Require Import HoTT.Types.Bool HoTT.Types.Prod HoTT.Basics.Decidable.
Require Import
  HoTTClasses.interfaces.canonical_names
  HoTTClasses.misc.util.

(* HoTT compat *)
Notation Decision := Decidable (only parsing).
Notation decide := dec.

Instance decide_stable : forall P, Decision P -> Stable P.
Proof.
intros P dec dn.
destruct dec as [p|n].
- assumption.
- apply Empty_rect. auto.
Qed.

Ltac case_decide := match goal with
  | H : context [@decide ?P ?dec] |- _ => case (@decide P dec) in *
  | |- context [@decide ?P ?dec] => case (@decide P dec) in *
  end.

Ltac solve_trivial_decision :=
  match goal with
  | [ |- Decision (?P) ] => apply _
  | [ |- ?P + (~?P) ] => change (Decision P); apply _
  end.

Ltac solve_decision :=
  first [solve_trivial_decision
    | unfold Decision; decide equality; solve_trivial_decision].

Instance decision_proper (P Q : Type) (PiffQ : P <-> Q) (P_dec : Decision P)
  : Decision Q.
Proof.
destruct P_dec as [p|np].
- left; apply PiffQ;assumption.
- right; intros q. apply np;apply PiffQ;assumption.
Defined.

Definition bool_decide@{i} (P : Type@{i}) `{dec : !Decision P} : bool
 := if dec then true else false.

Lemma bool_decide_true@{i} {P:Type@{i} } `{dec : Decision P}
  : iff@{Ularge i Ularge} (bool_decide P = true) P.
Proof.
unfold bool_decide. split; intro X; destruct dec as [p|np];auto.
- apply false_ne_true in X. destruct X.
- destruct (np X).
Qed.

Lemma bool_decide_false@{i} {P:Type@{i} } `{dec : !Decision P}
  : iff@{Ularge i Ularge} (bool_decide P = false) (~P).
Proof.
unfold bool_decide. split; intro X; destruct dec as [p|np]; auto.
- apply true_ne_false in X. destruct X.
- destruct (X p).
Qed.

(*
  Because [vm_compute] evaluates terms in [PROP] eagerly
  and does not remove dead code we
  need the decide_rel hack. Suppose we have [(x = y) =def  (f x = f y)], now:
     bool_decide (x = y) -> bool_decide (f x = f y) -> ...
  As we see, the dead code [f x] and [f y] is actually evaluated,
  which is of course an utter waste.
  Therefore we introduce decide_rel and bool_decide_rel.
     bool_decide_rel (=) x y -> bool_decide_rel (fun a b => f a = f b) x y -> ...
  Now the definition of equality remains under a lambda and
  our problem does not occur anymore!
*)

Definition decide_rel `(R : A -> B -> Type)
  {dec : forall x y, Decision (R x y)} (x : A) (y : B)
  : Decision (R x y)
  := dec x y.

Definition bool_decide_rel `(R : relation A)
  {dec : forall x y, Decision (R x y)} : A -> A -> Bool
  := fun x y => if dec x y then true else false.

Lemma bool_decide_rel_true `(R : relation A)
  {dec : forall x y, Decision (R x y)} :
  forall x y, bool_decide_rel R x y = true <-> R x y.
Proof.
unfold bool_decide_rel. split; intro X; destruct dec as [p|np];auto.
- apply false_ne_true in X;destruct X.
- destruct (np X).
Qed.

Lemma bool_decide_rel_false `(R : relation A)`{dec : forall x y, Decision (R x y)}
  : forall x y, bool_decide_rel R x y = false <-> ~R x y.
Proof.
unfold bool_decide_rel. split; intro X; destruct dec as [p|np];auto.
- apply true_ne_false in X;destruct X.
- destruct (X p).
Qed.

Definition decision_from_bool_decide {P b} (prf : b = true <-> P) :
  Decision P.
Proof.
destruct b.
- left;apply prf;auto.
- right;intro p.
  apply prf in p. apply false_ne_true in p.
  destruct p.
Qed.

Instance decide_eqb `{DecidablePaths A} : Eqb A
  := fun a b => if decide_rel (=) a b then true else false.

Lemma decide_eqb_ok@{i} {A:Type@{i} } `{DecidablePaths A} :
  forall a b, iff@{Ularge i Ularge} (a =? b = true) (a = b).
Proof.
unfold eqb,decide_eqb.
intros a b;destruct (decide_rel (=) a b) as [E1|E1];split;intros E2;auto.
- destruct (false_ne_true E2).
- destruct (E1 E2).
Qed.

Instance prod_eq_dec `(A_dec : forall x y : A, Decision (x = y))
     `(B_dec : forall x y : B, Decision (x = y))
     : forall x y : (A * B)%type, Decision (x = y).
Proof.
intros [x1 x2] [y1 y2].
destruct (A_dec x1 y1) as [?|na].
- destruct (B_dec x2 y2) as [?|nb].
  + left.
    apply path_prod';assumption.
  + right. intros e.
    apply equiv_path_prod in e;simpl in e.
    apply nb. apply e.
- right. intros e.
  apply equiv_path_prod in e;simpl in e.
  apply na;apply e.
Qed.


Instance or_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P \/ Q).
Proof.
destruct P_dec as [p|np].
- left;left;assumption.
- destruct Q_dec as [q|nq].
  + left;right;assumption.
  + right. intros [p|q];auto.
Qed.

Instance Unit_dec: Decision Unit := inl tt.
Instance Empty_dec: Decision Empty := inr id.
