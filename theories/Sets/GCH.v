From HoTT Require Import Basics TruncType abstract_algebra.
From HoTT Require Import PropResizing.PropResizing.
From HoTT Require Import Spaces.Nat.

Open Scope type.


(** * Formulation of GCH *)

Definition inject X Y :=
  { f : X -> Y | IsInjective f }.

Lemma inject_refl X :
  inject X X.
Proof.
  exists (fun x => x). intros x x'. easy.
Qed.

Lemma inject_trans X Y Z :
  inject X Y -> inject Y Z -> inject X Z.
Proof.
  intros [f Hf] [g Hg]. exists (fun x => g (f x)).
  now intros x x' H % Hg % Hf.
Qed.

Definition hinject X Y :=
  hexists (@IsInjective X Y).

Lemma hinject_trans X Y Z :
  hinject X Y -> hinject Y Z -> hinject X Z.
Proof.
  intros H1 H2.
  eapply merely_destruct; try apply H1. intros [f Hf].
  eapply merely_destruct; try apply H2. intros [g Hg].
  apply tr. exists (fun x => g (f x)). now intros x x' H % Hg % Hf.
Qed.

Definition infinite X :=
  inject nat X.

Definition GCH :=
  forall X Y : HSet, infinite X -> hinject X Y -> hinject Y (X -> HProp) -> hinject Y X + hinject (X -> HProp) Y.



(** * GCH is a proposition *)

Instance hProp_impred {FE : Funext} X (F : X -> Type) :
  (forall x, IsHProp (F x)) -> IsHProp (forall x, F x).
Proof.
  intros H. apply hprop_allpath. intros f g.
  apply path_forall. intros x. apply H.
Qed.

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

Lemma GCH_hProp {PR : PropResizing} {FE : Funext} :
  IsHProp GCH.
Proof.
  repeat (apply hProp_impred; intros).
  apply hprop_allpath. intros [H|H] [H'|H'].
  - enough (H = H') as ->; trivial. apply (hinject x0 x).
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj x); trivial. now apply hinject_trans with x0.
  - apply Empty_rec. eapply merely_destruct; try eapply (Cantor_inj x); trivial. now apply hinject_trans with x0.
  - enough (H = H') as ->; trivial. apply (hinject (x -> HProp) x0).
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

  Definition Y :=
    { p : X -> HProp | sing p \/ (P + ~ P) }.

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

  Lemma sig_inj {Z} (r : Z -> HProp) :
    IsInjective (@proj1 Z r).
  Proof.
    intros [p Hp] [q Hq]; cbn.
    intros ->. unshelve eapply path_sigma; cbn.
    - reflexivity.
    - cbn. apply (r q).
  Qed.

  Lemma Y_inj :
    (P + ~ P) -> inject (X -> HProp) Y.
  Proof.
    intros HP. unshelve eexists.
    - intros p. exists p. apply tr. now right.
    - intros p q. intros H. change p with ((exist (fun r => sing r \/ (P + ~ P)) p (tr (inr HP))).1).
      rewrite H. cbn. reflexivity.
  Qed.

  Lemma IsInjective_trans {X' Y Z} (f : X' -> Y) (g : Y -> Z) :
    IsInjective f -> IsInjective g -> IsInjective (fun x => g (f x)).
  Proof.
    intros HF HG x y H. now apply HF, HG.
  Qed.

  Theorem CH_LEM :
    (inject X Y -> inject Y (X -> HProp) -> ~ (inject Y X) -> hinject (X -> HProp) Y) -> P \/ ~ P.
  Proof.
    intros ch. eapply merely_destruct; try apply ch.
    - unshelve eexists.
      + intros x. exists (hpaths x). apply tr. left. exists x. reflexivity.
      + intros x y. intros H % pr1_path. cbn in H. change (hpaths x y). now rewrite H.
    - exists (@proj1 _ _). now apply sig_inj.
    - intros H. assert (HP' : ~ ~ (P + ~ P)).
      { intros HP. apply HP. right. intros p. apply HP. now left. }
      apply HP'. intros HP % Y_inj. clear HP'.
      apply Cantor_inj with X. now eapply (inject_trans _ _ _ HP).
    - intros [i Hi]. destruct (Cantor_sing (fun p => @proj1 _ _ (i p))) as [p HP].
      + apply IsInjective_trans; trivial. now apply sig_inj.
      + destruct (i p) as [q Hq]; cbn in *.
        eapply merely_destruct; try apply Hq.
        intros [H|H]; try now apply tr.
  Qed.

End LEM.

Theorem GCH_LEM {PR : PropResizing} {UA : Univalence} :
  GCH -> (forall P : HProp, P \/ ~ P).
Proof.
  intros gch P. eapply (CH_LEM (Build_HSet nat)); try exact _. intros H1 H2 H3.
  destruct (gch (Build_HSet nat) (Build_HSet (Y (Build_HSet nat) P))) as [H|H].
  - cbn. exists idmap. apply isinj_idmap.
  - apply tr. apply H1.
  - apply tr. apply H2.
  - apply Empty_rec. eapply merely_destruct; try apply H. apply H3.
  - apply H.
Qed.
