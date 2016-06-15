Require Import HoTT.Types.Bool HoTT.Types.Prod HoTT.Basics.Decidable.
Require Import
  HoTTClasses.interfaces.canonical_names HoTTClasses.misc.util.

(* HoTT compat *)
Notation Decision := Decidable (only parsing).
Notation decide := dec.

Instance decide_stable : forall P, Decision P -> Stable P.
Proof.
intros P dec dn.
destruct dec as [p|n].
- assumption.
- apply False_rect. auto.
Qed.

Ltac case_decide := match goal with
  | H : context [@decide ?P ?dec] |- _ => case (@decide P dec) in *
  | |- context [@decide ?P ?dec] => case (@decide P dec) in *
  end.

Ltac solve_trivial_decision :=
  match goal with
  | [ |- Decision (?P) ] => apply _
  | [ |- ?P + (¬?P) ] => change (Decision P); apply _
  end.

Ltac solve_decision :=
  first [solve_trivial_decision | unfold Decision; decide equality; solve_trivial_decision].

Instance decision_proper (P Q : Type) (PiffQ : P ↔ Q) (P_dec : Decision P)
  : Decision Q.
Proof.
destruct P_dec as [p|np].
- left; apply PiffQ;assumption.
- right; intros q. apply np;apply PiffQ;assumption.
Defined.

Definition bool_decide (P : Type) `{dec : !Decision P} : Bool
 := if dec then true else false.

Lemma bool_decide_true `{dec : Decision P} : bool_decide P = true ↔ P.
Proof.
unfold bool_decide. split; intro X; destruct dec as [p|np];auto.
- apply false_ne_true in X. destruct X.
- destruct (np X).
Qed.

Lemma bool_decide_false `{dec : !Decision P} : bool_decide P = false ↔ ¬P.
Proof.
unfold bool_decide. split; intro X; destruct dec as [p|np]; auto.
- apply true_ne_false in X. destruct X.
- destruct (X p).
Qed.

(*
  Because [vm_compute] evaluates terms in [PROP] eagerly and does not remove dead code we
  need the decide_rel hack. Suppose we have [(x = y) =def  (f x = f y)], now:
     bool_decide (x = y) → bool_decide (f x = f y) → ...
  As we see, the dead code [f x] and [f y] is actually evaluated, which is of course an utter waste.
  Therefore we introduce decide_rel and bool_decide_rel.
     bool_decide_rel (=) x y → bool_decide_rel (λ a b, f a = f b) x y → ...
  Now the definition of equality remains under a lambda and our problem does not occur anymore!
*)

Definition decide_rel `(R : A → B → Type) {dec : ∀ x y, Decision (R x y)} (x : A) (y : B)
  : Decision (R x y)
  := dec x y.

Definition bool_decide_rel `(R : relation A) {dec : ∀ x y, Decision (R x y)} : A → A → Bool
  := λ x y, if dec x y then true else false.

Lemma bool_decide_rel_true `(R : relation A) {dec : ∀ x y, Decision (R x y)} :
  ∀ x y, bool_decide_rel R x y = true ↔ R x y.
Proof.
unfold bool_decide_rel. split; intro X; destruct dec as [p|np];auto.
- apply false_ne_true in X;destruct X.
- destruct (np X).
Qed.

Lemma bool_decide_rel_false `(R : relation A)`{dec : ∀ x y, Decision (R x y)} :
  ∀ x y, bool_decide_rel R x y = false ↔ ¬R x y.
Proof.
unfold bool_decide_rel. split; intro X; destruct dec as [p|np];auto.
- apply true_ne_false in X;destruct X.
- destruct (X p).
Qed.

Definition decision_from_bool_decide {P b} (prf : b = true ↔ P) :
  Decision P.
Proof.
destruct b.
- left;apply prf;auto.
- right;intro p.
  apply prf in p. apply false_ne_true in p.
  destruct p.
Qed.

Instance prod_eq_dec `(A_dec : ∀ x y : A, Decision (x = y))
     `(B_dec : ∀ x y : B, Decision (x = y)) : ∀ x y : A * B, Decision (x = y).
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


Instance or_dec `(P_dec : Decision P) `(Q_dec : Decision Q) : Decision (P ∨ Q).
Proof.
destruct P_dec as [p|np].
- left;left;assumption.
- destruct Q_dec as [q|nq].
  + left;right;assumption.
  + right. intros [p|q];auto.
Qed.

Instance is_Some_dec `(x : option A) : Decision (is_Some x).
Proof.
destruct x;simpl;red;auto.
Qed.

Instance is_None_dec `(x : option A) : Decision (is_None x).
Proof.
destruct x;simpl;red;auto.
Qed.

Instance option_eq_dec `(A_dec : ∀ x y : A, Decision (x ≡ y))
     : ∀ x y : option A, Decision (x ≡ y).
Proof.
intros [x|] [y|].
- destruct (decide (x = y)) as [e|n].
  + left.
    apply ap. assumption.
  + right.
    intros H. apply n.
    apply (ap (fun opt => match opt with None => x | Some z => z end)) in  H.
    simpl in H. assumption.
- right.
  intros H. apply symmetry in H.
  apply None_ne_Some in H. assumption.
- right;intros H.
  apply None_ne_Some in H. assumption.
- left;reflexivity.
Qed.

Instance True_dec: Decision True := left tt.
Instance False_dec: Decision False := right id.
