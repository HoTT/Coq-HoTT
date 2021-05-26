From HoTT Require Import Basics TruncType abstract_algebra.
From HoTT Require Import PropResizing.PropResizing.
From HoTT Require Import Spaces.Nat.

From HoTT.Sets Require Import Cardinality.

Open Scope type.


(** * Formulation of GCH *)

(* GCH states that for any infinite set X with Y between X and P(X) either Y embeds into X or P(X) embeds into Y. *)

Definition GCH :=
  forall X Y : HSet, infinite X -> hinject X Y -> hinject Y (X -> HProp) -> hinject Y X + hinject (X -> HProp) Y.



(** * GCH is a proposition *)

Lemma Cantor_inj {PR : PropResizing} {FE : Funext} X :
  ~ inject (X -> HProp) X.
Proof.
  intros [i HI]. pose (p n := Build_HProp (resize_hprop (forall q, i q = n -> ~ q n))).
  enough (Hp : p (i p) <-> ~ p (i p)).
  { apply Hp; apply Hp; intros H; now apply Hp. }
  unfold p at 1. split.
  - intros H. apply equiv_resize_hprop in H. apply H. reflexivity.
  - intros H. apply equiv_resize_hprop. intros q -> % HI. apply H.
Qed.

(* The concluding disjunction of GCH is excluse since otherwise we'd obtain an injection of P(X) into X. *)

Lemma hprop_GCH {PR : PropResizing} {FE : Funext} :
  IsHProp GCH.
Proof.
  repeat (nrapply istrunc_forall; intros).
  apply hprop_allpath. intros [H|H] [H'|H'].
  - enough (H = H') as ->; trivial. apply (hinject a0 a).
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj a); trivial. now apply hinject_trans with a0.
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj a); trivial. now apply hinject_trans with a0.
  - enough (H = H') as ->; trivial. apply (hinject (a -> HProp) a0).
Qed.



(** * GCH implies LEM *)

Section LEM.

  Variable X : HSet.
  Variable P : HProp.

  Context {PR : PropResizing}.
  Context {FE : Funext}.

  Definition hpaths (x y : X) :=
    Build_HProp (paths x y).

  Definition sing (p : X -> HProp) :=
    exists x, p = hpaths x.

  Let sings :=
    { p : X -> HProp | sing p \/ (P + ~ P) }.

  (* The main idea is that for a given set X and proposition P, the set sings fits between X and P(X).
     Then CH for X implies that either sings embeds into X (which can be refuted constructively),
     or that P(X) embeds into sings, from which we can extract a proof of P + ~P. *)  

  Lemma Cantor_sing (i : (X -> HProp) -> (X -> HProp)) :
    IsInjective i -> exists p, ~ sing (i p).
  Proof.
    intros HI. pose (p n := Build_HProp (resize_hprop (forall q, i q = hpaths n -> ~ q n))).
    exists p. intros [n HN]. enough (Hp : p n <-> ~ p n).
    { apply Hp; apply Hp; intros H; now apply Hp. }
    unfold p at 1. split.
    - intros H. apply equiv_resize_hprop in H. apply H, HN.
    - intros H. apply equiv_resize_hprop. intros q HQ. rewrite <- HN in HQ. now apply HI in HQ as ->.
  Qed.

  Lemma injective_proj1 {Z} (r : Z -> HProp) :
    IsInjective (@proj1 Z r).
  Proof.
    intros [p Hp] [q Hq]; cbn.
    intros ->. unshelve eapply path_sigma; cbn.
    - reflexivity.
    - cbn. apply (r q).
  Qed.

  Lemma inject_sings :
    (P + ~ P) -> inject (X -> HProp) sings.
  Proof.
    intros HP. unshelve eexists.
    - intros p. exists p. apply tr. now right.
    - intros p q. intros H. change p with ((exist (fun r => sing r \/ (P + ~ P)) p (tr (inr HP))).1).
      rewrite H. cbn. reflexivity.
  Qed.

  Theorem CH_LEM :
    (inject X sings -> inject sings (X -> HProp) -> ~ (inject sings X) -> hinject (X -> HProp) sings) -> P \/ ~ P.
  Proof.
    intros ch. eapply merely_destruct; try apply ch.
    - unshelve eexists.
      + intros x. exists (hpaths x). apply tr. left. exists x. reflexivity.
      + intros x y. intros H % pr1_path. cbn in H. change (hpaths x y). now rewrite H.
    - exists (@proj1 _ _). now apply injective_proj1.
    - intros H. assert (HP' : ~ ~ (P + ~ P)).
      { intros HP. apply HP. right. intros p. apply HP. now left. }
      apply HP'. intros HP % inject_sings. clear HP'.
      apply Cantor_inj with X. now eapply (inject_trans _ _ _ HP).
    - intros [i Hi]. destruct (Cantor_sing (fun p => @proj1 _ _ (i p))) as [p HP].
      + apply isinjective_Compose; trivial. now apply injective_proj1.
      + destruct (i p) as [q Hq]; cbn in *.
        eapply merely_destruct; try apply Hq.
        intros [H|H]; try now apply tr.
  Qed.

End LEM.

(* We can instantiate the previous lemma with nat to obtain GCH -> LEM. *)

Theorem GCH_LEM {PR : PropResizing} {UA : Univalence} :
  GCH -> (forall P : HProp, P \/ ~ P).
Proof.
  intros gch P. eapply (CH_LEM (Build_HSet nat)); try exact _. intros H1 H2 H3.
  pose (sings := { p : nat -> HProp | sing (Build_HSet nat) p \/ (P + ~ P) }).
  destruct (gch (Build_HSet nat) (Build_HSet sings)) as [H|H].
  - cbn. exists idmap. apply isinj_idmap.
  - apply tr. apply H1.
  - apply tr. apply H2.
  - apply Empty_rec. eapply merely_destruct; try apply H. apply H3.
  - apply H.
Qed.
