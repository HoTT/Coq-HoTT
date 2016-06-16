Require Import HoTT.Basics HoTT.Types.Bool.
Require Import
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.theory.additional_operations
  HoTTClasses.tactics.ring_quote
  HoTTClasses.theory.rings
  HoTTClasses.misc.decision.

Import Quoting.

Section content.

(* [C] is the scalar semiring: Z when working on rings,
   N on semirings, other sometimes. *)
Context `{SemiRing C} `{DecidablePaths C}.

(* [V] is the type of variables, ie we are defining polynomials [C[V]].
   It has a computable compare so we can normalise polynomials. *)
Context `{Trichotomy V Vlt}.

Inductive Pol :=
  | Pconst (c : C)
  | PX (P : Pol) (v : V) (Q : Pol).

(* Polynomials are supposed (at the meta level) to be in normal form:
   PX P v Q verifies
     + P <> 0
     + forall w in P, w <= v
     + forall w in Q, w <  v *)

Fixpoint Peqb P Q :=
  match P, Q with
  | Pconst c, Pconst d => c =? d
  | PX P1 v P2, PX Q1 w Q2 =>
    andb (v =? w) (andb (Peqb P1 Q1) (Peqb P2 Q2))
  | _, _ => false
  end.

Global Instance : Eqb Pol := Peqb.

Global Instance P0 : canonical_names.Zero Pol := Pconst 0.
Global Instance P1 : canonical_names.One Pol := Pconst 1.

Context `{SemiRing R} (phi : C -> R) `{!SemiRing_Morphism phi}.

Notation Vars V := (V -> R).

Fixpoint eval (vs : Vars V) (P : Pol) : R :=
  match P with
  | Pconst c => phi c
  | PX P v Q =>
    (eval vs P) * (vs v) + (eval vs Q)
  end.

Lemma andb_true : forall a b, andb a b = true -> a = true /\ b = true.
Proof.
intros [|] [|];simpl;auto.
Qed.

Lemma eval_eqb : forall P Q, P =? Q = true -> forall vs, eval vs P = eval vs Q.
Proof.
induction P as [c|P1 IHP1 v P2 IHP2];destruct Q as [d|Q1 w Q2];intros E vs;
change eqb with Peqb in E;simpl in E.
- simpl. apply ap. apply decide_eqb_ok;trivial.
- destruct (false_ne_true E).
- destruct (false_ne_true E).
- apply andb_true in E. destruct E as [E1 E2].
  apply andb_true in E2. destruct E2 as [E2 E3].
  simpl.
  apply compare_eqb_eq,tricho_compare_eq in E1.
  apply ap2;auto. apply ap2;auto.
Qed.

Lemma eval_0 : forall P, P =? 0 = true -> forall vs, eval vs P = 0.
Proof.
induction P;simpl;intros E vs.
- change eqb with Peqb in E;simpl in E.
  apply decide_eqb_ok in E. rewrite E.
  apply preserves_0.
- change eqb with Peqb in E;simpl in E.
  destruct (false_ne_true E).
Qed.

Fixpoint addC c P :=
  match P with
  | Pconst d => Pconst (c + d)
  | PX P v Q =>
    PX P v (addC c Q)
  end.

Lemma eval_addC vs : forall c P, eval vs (addC c P) = (phi c) + eval vs P.
Proof.
induction P;simpl.
- apply preserves_plus.
- rewrite IHP2.
  rewrite 2!plus_assoc. rewrite (plus_comm (phi c)).
  reflexivity.
Qed.

Definition mkPX P v Q :=
  if P =? 0 then Q else PX P v Q.

Lemma eval_mkPX vs : forall P v Q,
  eval vs (mkPX P v Q) = (eval vs P) * (vs v) + eval vs Q.
Proof.
intros. unfold mkPX.
pose proof (eval_0 P) as E.
destruct (P =? 0).
- rewrite E by split. rewrite mult_0_l,plus_0_l;reflexivity.
- reflexivity.
Qed.

Fixpoint mulC c P :=
  match P with
  | Pconst d => Pconst (c * d)
  | PX P v Q =>
    mkPX (mulC c P) v (mulC c Q)
  end.

Lemma eval_mulC vs : forall c P, eval vs (mulC c P) = (phi c) * eval vs P.
Proof.
induction P;simpl.
- apply preserves_mult.
- rewrite eval_mkPX.
  rewrite IHP1,IHP2,plus_mult_distr_l,mult_assoc. reflexivity.
Qed.

Fixpoint add P Q :=
  match P, Q with
  | Pconst c, _ => addC c Q
  | _, Pconst d => addC d P
  | PX P1 v P2, PX Q1 w Q2 =>
    (* P1 <= v, P2 < v, Q1 <= w, Q2 < w *)
    match v ?= w with
    | EQ =>
      mkPX (add P1 Q1) v (add P2 Q2)
    | LT =>
      PX Q1 w (PX P1 v (add P2 Q2))
    | GT =>
      PX P1 v (PX Q1 w (add P2 Q2))
    end
  end.

Lemma eval_add vs : forall P Q, eval vs (add P Q) = eval vs P + eval vs Q.
Proof.
induction P as [c | P1 IHP1 v P2 IHP2];intros Q.
- apply eval_addC.
- destruct Q as [d | Q1 w Q2].
  + simpl. rewrite <-plus_assoc.
    apply ap. rewrite plus_comm; apply eval_addC.
  + simpl.
    pose proof (tricho_compare_eq v w) as E.
    destruct (v ?= w).
    * simpl.
      rewrite IHP2.
      rewrite plus_assoc, (plus_comm (eval vs Q1 * vs w)).
      rewrite <-2!plus_assoc. apply ap.
      rewrite 2!plus_assoc. rewrite (plus_comm (eval vs P2)). reflexivity.
    * rewrite E by split;clear E;clear v.
      rewrite eval_mkPX.
      rewrite <-plus_assoc,(plus_assoc (eval vs P2)).
      rewrite (plus_comm (eval vs P2)).
      rewrite <-plus_assoc,plus_assoc.
      rewrite <-plus_mult_distr_r.
      rewrite IHP1,IHP2;reflexivity.
    * simpl.
      rewrite IHP2.
      rewrite <-plus_assoc. apply ap.
      rewrite 2!plus_assoc,(plus_comm (eval vs P2));reflexivity.
Qed.

Fixpoint mul P Q :=
  match P, Q with
  | Pconst c, _ => mulC c Q
  | _, Pconst d => mulC d P
  | PX P1 v P2, PX Q1 w Q2 =>
    (* P1 <= v, P2 < v, Q1 <= w, Q2 < w *)
    (* P1 Q1 v w + P1 Q2 v + P2 Q1 w + P2 Q2 *)
    match v ?= w with
    | EQ =>
      mkPX (mkPX (mul P1 Q1) v (add (mul P1 Q2) (mul P2 Q1))) v (mul P2 Q2)
    | LT =>
      (*  (P1 Q1 * w + P2 Q1) * w + (P1 Q2 * v + P2 Q2) *)
      mkPX (mkPX (mul P1 Q1) v (mul P2 Q1)) w (mkPX (mul P1 Q2) v (mul P2 Q2))
    | GT =>
      mkPX (mkPX (mul P1 Q1) w (mul P1 Q2)) v (mkPX (mul P2 Q1) w (mul P2 Q2))
    end
  end.

Lemma eval_mul vs : forall P Q, eval vs (mul P Q) = eval vs P * eval vs Q.
Proof.
induction P as [c | P1 IHP1 v P2 IHP2];intros Q.
- simpl. apply eval_mulC.
- destruct Q as [d | Q1 w Q2].
  + simpl. rewrite eval_mkPX,2!eval_mulC.
    rewrite <-mult_assoc,<-plus_mult_distr_l,mult_comm. reflexivity.
  + simpl.
    rewrite plus_mult_distr_l,plus_mult_distr_r.
    rewrite (plus_mult_distr_r _ _ (eval vs Q2)).
    rewrite <-IHP2.
    rewrite <-mult_assoc,(mult_assoc (vs v)),(mult_comm (vs v)).
    rewrite <-(mult_assoc (eval vs Q1)),mult_assoc,<-IHP1.
    rewrite (mult_assoc (eval vs P2)),<-IHP2.
    rewrite (mult_comm (eval vs P1)),<-(mult_assoc (vs v)),<-IHP1.
    pose proof (tricho_compare_eq v w) as E.
    destruct (v ?= w).
    * clear E.
      rewrite !eval_mkPX.
      rewrite plus_mult_distr_r.
      apply ap2;apply ap2;trivial;[|apply mult_comm].
      symmetry;apply mult_assoc.
    * rewrite E by split;rewrite !eval_mkPX.
      rewrite plus_mult_distr_r.
      rewrite eval_add. rewrite (plus_mult_distr_r (eval vs (mul P1 Q2))).
      rewrite (plus_comm (eval vs (mul P1 Q2) * _)).
      rewrite !plus_assoc. apply ap2;[apply ap2;[apply ap2|apply mult_comm]|];
      trivial.
      symmetry;apply mult_assoc.
    * clear E.
      rewrite !eval_mkPX.
      rewrite plus_mult_distr_r.
      rewrite <-plus_assoc,(plus_assoc (eval vs _ * vs v)).
      rewrite (plus_comm (eval _ _ * vs v)).
      rewrite !plus_assoc.
      apply ap2;apply ap2;trivial;[|apply mult_comm];apply ap2;trivial.
      rewrite (mult_comm (vs v));symmetry;apply mult_assoc.
Qed.

Fixpoint norm (e: Expr V) :=
  match e with
  | Var v => PX 1 v 0
  | Zero => 0
  | One => 1
  | Plus a b => add (norm a) (norm b)
  | Mult a b => mul (norm a) (norm b)
  end.

Lemma eval_norm vs : forall e, eval vs (norm e) = Quoting.eval _ vs e.
Proof.
induction e as [v| | |a IHa b IHb|a IHa b IHb];simpl.
- rewrite (preserves_1 (f:=phi)),(preserves_0 (f:=phi)),plus_0_r,mult_1_l.
  reflexivity.
- apply preserves_0.
- apply preserves_1.
- rewrite eval_add,IHa,IHb. reflexivity.
- rewrite eval_mul,IHa,IHb. reflexivity.
Qed.

End content.
