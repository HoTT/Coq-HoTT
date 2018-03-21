Require Import HoTT.Basics HoTT.Types.Bool.
Require Import
  HoTT.Classes.interfaces.abstract_algebra
  HoTT.Classes.theory.additional_operations
  HoTT.Classes.tactics.ring_quote
  HoTT.Classes.theory.rings.

Import Quoting.
Local Set Universe Minimization ToSet.

Section content.
Local Existing Instance almost_ring_semiring.
Local Existing Instance almostring_mor_sr_mor.

Universe UC.
Context {C : Type@{UC} } {V : Type0 }.

Inductive Pol : Type@{UC} :=
  | Pconst (c : C)
  | PX (P : Pol) (v : V) (Q : Pol).

(* [C] is the scalar semiring: Z when working on rings,
   N on semirings, other sometimes. *)
Context `{AlmostRing C} `{DecidablePaths C}.

(* [V] is the type of variables, ie we are defining polynomials [C[V]].
   It has a computable compare so we can normalise polynomials. *)
Context `{Trichotomy@{Set Set Set} V Vlt}.

(* Polynomials are supposed (at the meta level) to be in normal form:
   PX P v Q verifies
     + P <> 0
     + forall w in P, w <= v
     + forall w in Q, w <  v *)

Fixpoint Peqb P Q : Bool :=
  match P, Q with
  | Pconst c, Pconst d => c =? d
  | PX P1 v P2, PX Q1 w Q2 =>
    andb (v =? w) (andb (Peqb P1 Q1) (Peqb P2 Q2))
  | _, _ => false
  end.

Global Instance Peqb_instance : Eqb Pol := Peqb.
Arguments Peqb_instance _ _ /.

Global Instance P0 : canonical_names.Zero Pol := Pconst 0.
Global Instance P1 : canonical_names.One Pol := Pconst 1.

Universe UR.
Context {R : Type@{UR} } `{AlmostRing R}
  (phi : C -> R) `{!AlmostRingPreserving phi}.

Notation Vars V := (V -> R).

Fixpoint eval (vs : Vars V) (P : Pol) : R :=
  match P with
  | Pconst c => phi c
  | PX P v Q =>
    (eval vs P) * (vs v) + (eval vs Q)
  end.

Lemma andb_true : forall a b : Bool, andb a b = true -> a = true /\ b = true.
Proof.
intros [|] [|];simpl;auto.
Qed.

Lemma eval_eqb' : forall P Q : Pol, P =? Q = true ->
  forall vs : Vars V, eval vs P = eval vs Q.
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

Definition eval_eqb@{} := eval_eqb'@{Ularge}.

Lemma eval_0' : forall P, P =? 0 = true -> forall vs, eval vs P = 0.
Proof.
induction P;simpl;intros E vs.
- change eqb with Peqb in E;simpl in E.
  apply decide_eqb_ok in E. rewrite E.
  apply preserves_0.
- change eqb with Peqb in E;simpl in E.
  destruct (false_ne_true E).
Qed.

Definition eval_0@{} := eval_0'@{Ularge}.

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

(* c * v + Q *)
Fixpoint addX' c v Q :=
  match Q with
  | Pconst d => PX (Pconst c) v Q
  | PX Q1 w Q2 =>
    match v ?= w with
    | LT =>
      PX Q1 w (addX' c v Q2)
    | EQ =>
      PX (addC c Q1) v Q2
    | GT => PX (Pconst c) v Q
    end
  end.

Definition addX c v Q := if c =? 0 then Q else addX' c v Q.

Lemma eval_addX'@{} vs : forall c (v:V) Q,
  eval vs (addX' c v Q) = phi c * vs v + eval vs Q.
Proof.
induction Q as [d|Q1 IH1 w Q2 IH2].
- simpl.
  reflexivity.
- simpl.
  pose proof (tricho_compare_eq v w) as E.
  destruct (v ?= w);[clear E|rewrite <-E by split;clear E w|clear E].
  + simpl. rewrite IH2.
    rewrite 2!plus_assoc. apply ap2;trivial.
    apply plus_comm.
  + simpl. rewrite eval_addC.
    rewrite plus_mult_distr_r.
    symmetry;apply plus_assoc.
  + simpl. reflexivity.
Qed.

Lemma eval_addX vs : forall c (v:V) Q,
  eval vs (addX c v Q) = phi c * vs v + eval vs Q.
Proof.
intros. unfold addX.
pose proof (decide_eqb_ok c 0) as E.
destruct (c =? 0).
- rewrite (fst E) by split. rewrite (preserves_0 (f:=phi)).
  rewrite mult_0_l,plus_0_l. split.
- apply eval_addX'.
Qed.

Definition PXguard@{} P v Q := if eqb P 0 then Q else PX P v Q.

Lemma eval_PXguard vs : forall P (v:V) Q,
  eval vs (PXguard P v Q) = eval vs P * vs v + eval vs Q.
Proof.
intros. unfold PXguard.
pose proof (eval_0 P) as E.
destruct (P =? 0).
- rewrite E by split.
  rewrite mult_0_l,plus_0_l. split.
- reflexivity.
Qed.

Fixpoint mulC c P :=
  match P with
  | Pconst d => Pconst (c * d)
  | PX P v Q =>
    (* in some semirings we can have zero divisors, so P' might be zero *)
    PXguard (mulC c P) v (mulC c Q)
  end.

Lemma eval_mulC vs : forall c P, eval vs (mulC c P) = (phi c) * eval vs P.
Proof.
induction P as [d | P1 IH1 v P2 IH2];simpl.
- apply preserves_mult.
- rewrite eval_PXguard.
  rewrite IH1,IH2,plus_mult_distr_l,mult_assoc. reflexivity.
Qed.

(* if P <= v, P <> 0, and addP Q = P + Q then P * v + Q *)
Fixpoint add_aux addP P v Q :=
  match Q with
  | Pconst _ => PX P v Q
  | PX Q1 w Q2 =>
    match v ?= w with
    | LT =>
      PX Q1 w (add_aux addP P v Q2)
    | EQ => PXguard (addP Q1) v Q2
    | GT =>
      PX P v Q
    end
  end.

Fixpoint add P Q :=
  match P with
  | Pconst c => addC c Q
  | PX P1 v P2 => add_aux (add P1) P1 v (add P2 Q)
  end.

Lemma eval_add_aux vs P addP
  (Eadd : forall Q, eval vs (addP Q) = eval vs P + eval vs Q)
  : forall (v:V) Q, eval vs (add_aux addP P v Q) = eval vs P * vs v + eval vs Q.
Proof.
induction Q as [d|Q1 IH1 w Q2 IH2].
- simpl. reflexivity.
- simpl.
  pose proof (tricho_compare_eq v w) as E.
  destruct (v ?= w);[clear E|rewrite <-E by split;clear E w|clear E].
  + simpl.
    rewrite IH2.
    rewrite 2!plus_assoc. rewrite (plus_comm (eval vs Q1 * vs w)).
    reflexivity.
  + rewrite eval_PXguard. rewrite Eadd.
    rewrite plus_mult_distr_r.
    symmetry;apply plus_assoc.
  + simpl. reflexivity.
Qed.

Lemma eval_add' vs : forall P Q, eval vs (add P Q) = eval vs P + eval vs Q.
Proof.
induction P as [c|P1 IH1 v P2 IH2];intros Q.
- simpl. apply eval_addC.
- simpl. rewrite eval_add_aux;auto.
  rewrite IH2. apply plus_assoc.
Qed.

Definition eval_add@{} := eval_add'@{Ularge}.

Fixpoint mulX v P :=
  match P with
  | Pconst c => addX c v 0
  | PX P1 w P2 =>
    match v ?= w with
    | LT =>
      PX (mulX v P1) w (mulX v P2)
    | _ => PX P v 0
    end
  end.

Lemma eval_mulX@{} vs : forall (v:V) (P:Pol), eval vs (mulX v P) = eval vs P * vs v.
Proof.
induction P as [c|P1 IH1 w P2 IH2].
- simpl. rewrite eval_addX.
  simpl. rewrite (preserves_0 (f:=phi)),plus_0_r.
  split.
- simpl.
  pose proof (tricho_compare_eq v w) as E.
  destruct (v ?= w);[clear E|rewrite <-E by split;clear E w|clear E].
  + simpl.
    rewrite plus_mult_distr_r,IH1,IH2.
    apply ap2;trivial.
    rewrite <-2!mult_assoc;apply ap,mult_comm.
  + simpl. rewrite (preserves_0 (f:=phi)),plus_0_r.
    reflexivity.
  + simpl. rewrite (preserves_0 (f:=phi)),plus_0_r.
    reflexivity.
Qed.

Definition mkPX P v Q := add (mulX v P) Q.

Lemma eval_mkPX vs : forall P v Q,
  eval vs (mkPX P v Q) = (eval vs P) * (vs v) + eval vs Q.
Proof.
intros. unfold mkPX.
rewrite eval_add,eval_mulX. reflexivity.
Qed.

Fixpoint mul P Q :=
  match P, Q with
  | Pconst c, _ => mulC c Q
  | _, Pconst d => mulC d P
  | PX P1 v P2, PX Q1 w Q2 =>
    (* P1 Q1 v w + P1 Q2 v + P2 Q1 w + P2 Q2 *)
    add (mulX v (add (mulX w (mul P1 Q1)) (mul P1 Q2)))
        (add (mulX w (mul P2 Q1)) (mul P2 Q2))
  end.

Lemma eval_mul' vs : forall P Q, eval vs (mul P Q) = eval vs P * eval vs Q.
Proof.
induction P as [c | P1 IHP1 v P2 IHP2];[apply eval_mulC|].
destruct Q as [d | Q1 w Q2].
- change (mul (PX P1 v P2) (Pconst d)) with (mulC d (PX P1 v P2)).
  rewrite eval_mulC. apply mult_comm.
- simpl.
  rewrite plus_mult_distr_r,!plus_mult_distr_l.
  repeat (rewrite eval_add || rewrite eval_mulX).
  rewrite plus_mult_distr_r,(plus_mult_distr_l (eval vs P2)).
  rewrite IHP1,IHP2.
  apply ap2;apply ap2.
  + rewrite <-!mult_assoc.
    apply ap.
    rewrite (mult_comm (vs v)). apply mult_assoc.
  + rewrite <-mult_assoc,(mult_comm (vs v)),mult_assoc.
    rewrite IHP1;reflexivity.
  + symmetry;apply mult_assoc.
  + auto.
Qed.

Definition eval_mul@{} := eval_mul'@{Ularge}.

Fixpoint toPol (e: Expr V) :=
  match e with
  | Var v => PX 1 v 0
  | Zero => 0
  | One => 1
  | Plus a b => add (toPol a) (toPol b)
  | Mult a b => mul (toPol a) (toPol b)
  | Neg a => mulC (almost_negate 1) (toPol a)
  end.

Lemma eval_toPol@{} vs : forall e : Expr V,
  eval vs (toPol e) = Quoting.eval _ vs e.
Proof.
induction e as [v| | |a IHa b IHb|a IHa b IHb|a IHa];simpl.
- rewrite (preserves_1 (f:=phi)),(preserves_0 (f:=phi)),plus_0_r,mult_1_l.
  reflexivity.
- apply preserves_0.
- apply preserves_1.
- rewrite eval_add,IHa,IHb. reflexivity.
- rewrite eval_mul,IHa,IHb. reflexivity.
- rewrite eval_mulC. rewrite (almostring_mor_neg (f:=phi)),preserves_1.
  rewrite <-almost_ring_neg_pr. apply ap,IHa.
Qed.

End content.
