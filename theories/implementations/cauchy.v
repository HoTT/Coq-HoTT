Require Import
  HoTT.Basics.Decidable
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.field_of_fractions
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.theory.rationals.

Module Export Cauchy.

Section VarSec.

Context `{Rationals Q} `{Qap : Apart Q} `{Qlt : Lt Q} `{Qle : Le Q}
  `{!FullPseudoSemiRingOrder (_:Le Q) (_:Lt Q)}.

Record Qpos := mkQpos { pos : Q; is_pos : 0 < pos }.
Notation "Q+" := Qpos.

Instance : Cast Qpos Q := pos.

Lemma Qpos_plus_pr : forall a b : Qpos, 0 < 'a + 'b.
Proof.
intros.
apply semirings.pos_plus_compat;apply is_pos.
Qed.

Instance Qpos_plus : Plus Qpos := fun a b => mkQpos _ (Qpos_plus_pr a b).

Lemma Qpos_eq : forall a b : Qpos, ' a = ' b -> a = b.
Proof.
intros [a pa] [b pb] E.
change (a=b) in E.
destruct E. apply ap.
apply path_ishprop.
Qed.

Private Inductive real : Type :=
  | rat : Q -> real
  | lim' : forall (f : Qpos -> real),
    (forall d e : Qpos, equiv' (d+e) (f d) (f e)) -> real

with equiv' : Qpos -> real -> real -> Type :=
  | equiv_rat_rat' : forall (q r : Q) (e : Qpos),
      - (' e : Q) < q + (- r) < ' e ->
      equiv' e (rat q) (rat r)
  | equiv_rat_lim' : forall q y Hy (e d d' : Qpos),
      e = d + d' ->
      equiv' d' (rat q) (y d) ->
      equiv' e (rat q) (lim' y Hy)
  | equiv_lim_rat' : forall x Hx r (e d d' : Qpos),
      e = d + d' ->
      equiv' d' (x d) (rat r) ->
      equiv' e (lim' x Hx) (rat r)
  | equiv_lim_lim' : forall x Hx y Hy (e d n e' : Qpos),
      e = d + n + e' ->
      equiv' e' (x d) (y n) ->
      equiv' e (lim' x Hx) (lim' y Hy)
.

Class Requiv e u v := requiv : equiv' e u v.

Axiom equiv_path : forall (u v : real) (u_eq_v : forall e, Requiv e u v), u = v.
Axiom equiv_hprop : forall e u v, IsHProp (Requiv e u v).
Global Existing Instance equiv_hprop.

Record Approximation :=
  { approximate :> Qpos -> real
  ; approx_equiv : forall d e, Requiv (d+e) (approximate d) (approximate e) }.
Existing Instance approx_equiv.

Definition lim (x : Approximation) : real :=
  lim' x (fun _ _ => requiv).

Definition equiv_rat_rat : forall (q r : Q) (e : Qpos),
  - (' e : Q) < q + (- r) < ' e ->
  Requiv e (rat q) (rat r)
  := equiv_rat_rat'.

Definition equiv_rat_lim : forall q (y:Approximation) (e d d' : Qpos),
  e = d + d' ->
  Requiv d' (rat q) (y d) ->
  Requiv e (rat q) (lim y).
Proof.
intros. eapply equiv_rat_lim';eauto.
Defined.

Definition equiv_lim_rat : forall (x:Approximation) r (e d d' : Qpos),
  e = d + d' ->
  Requiv d' (x d) (rat r) ->
  Requiv e (lim x) (rat r).
Proof. intros;eapply equiv_lim_rat';eauto. Defined.

Definition equiv_lim_lim : forall (x y : Approximation) (e d n e' : Qpos),
  e = d + n + e' ->
  Requiv e' (x d) (y n) ->
  Requiv e (lim x) (lim y).
Proof.
intros;eapply equiv_lim_lim';eauto.
Defined.

Record DApproximation (A : real -> Type)
  (B : forall x y : real, A x -> A y -> forall e `{Requiv e x y}, Type)
  (x : Approximation) :=
  { dapproximation :> forall e, A (x e)
  ; dapproximation_correct :
    forall d e, B (x d) (x e) (dapproximation d) (dapproximation e) (d+e) }.

Record Inductors (A : real -> Type)
  (B : forall x y : real, A x -> A y -> forall e `{Requiv e x y}, Type) :=
  { ind_rat : forall q, A (rat q)
  ; ind_lim : forall (x:Approximation) (a : DApproximation A B x),
    A (lim x)

  ; ind_path_A : forall u v (u_equiv_v : forall e, Requiv e u v),
    forall (a : A u) (b : A v), (forall e, B u v a b e) ->
    equiv_path u v (fun _ => requiv) # a = b

  ; ind_rat_rat : forall q r e (Hqr : - ' e < q + (- r) < ' e),
      @B (rat q) (rat r) (ind_rat q) (ind_rat r) e (equiv_rat_rat _ _ _ Hqr)
  ; ind_rat_lim : forall q d d' e y (b : DApproximation A B y)
      (He : e = d + d')
      (Hclose : Requiv d' (rat q) (y d)),
      B (rat q) (y d) (ind_rat q) (b d) d' ->
      @B (rat q) (lim y) (ind_rat q) (ind_lim y b) e
         (equiv_rat_lim _ _ _ _ _ He _)
   ; ind_lim_rat : forall r d d' e x (a : DApproximation A B x)
      (He : e = d + d')
      (Hclose : Requiv d' (x d) (rat r)),
      B (x d) (rat r) (a d) (ind_rat r) d' ->
      @B (lim x) (rat r) (ind_lim x a) (ind_rat r) e
         (equiv_lim_rat _ _ _ _ _ He _)
   ; ind_lim_lim : forall x y (a : DApproximation A B x) (b : DApproximation A B y)
      e d n e' (He : e = d + n + e')
      (Hclose : Requiv e' (x d) (y n)),
      B (x d) (y n) (a d) (b n) e' ->
      @B (lim x) (lim y) (ind_lim x a) (ind_lim y b) e
         (equiv_lim_lim _ _ _ _ _ _ He _)

   ; ind_hprop_B : forall x y a b e xi, IsHProp (@B x y a b e xi) }.

Arguments ind_rat {_ _} _ _.
Arguments ind_lim {_ _} _ _ _.
Arguments ind_rat_rat {_ _} _ _ _ _ _.
Arguments ind_rat_lim {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_rat {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_lim {_ _} _ _ _ _ _ _ _ _ _ _ _ _.

Section induction.
Variable A : real -> Type.
Variable B : forall x y : real, A x -> A y -> forall e `{Requiv e x y}, Type.

Definition real_rect : Inductors A B -> forall x : real, A x :=
  fun I x =>
  fix real_rect (x : real) {struct x} : Inductors A B -> A x :=
    match x return (Inductors A B -> A x) with
    | rat q => fun I => ind_rat I q
    | lim' f Hf => fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim I x a
    end
  with equiv_rect (x y : real) (e : Qpos) (xi : Requiv e x y) {struct xi}
    : forall I : Inductors A B, @B x y (real_rect x I) (real_rect y I) e xi :=
    match xi in equiv' e' x' y' return
      (forall I : Inductors A B,
        @B x' y' (real_rect x' I) (real_rect y' I) e' xi) with
    | equiv_rat_rat' q r e H => fun I => ind_rat_rat I q r e H
    | equiv_rat_lim' q f Hf e d d' He xi =>
      fun I =>
      let y := Build_Approximation f Hf in
      let b := Build_DApproximation A B y (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_rat_lim I q d d' e y b He xi (equiv_rect _ _ _ xi I)
    | equiv_lim_rat' f Hf r e d d' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim_rat I r d d' e x a He xi (equiv_rect _ _ _ xi I)
    | equiv_lim_lim' f Hf g Hg e d n e' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      let y := Build_Approximation g Hg in
      let b := Build_DApproximation A B y (fun e => real_rect (g e) I)
        (fun d e => equiv_rect (g d) (g e) _ (Hg d e) I) in
      ind_lim_lim I x y a b e d n e' He xi (equiv_rect _ _ _ xi I)
    end
  for real_rect x I.

Definition equiv_rect : forall (I : Inductors A B)
  (x y : real) (e : Qpos) (xi : Requiv e x y),
  @B x y (real_rect I x) (real_rect I y) e xi :=
  fun I x y e xi =>
  fix real_rect (x : real) {struct x} : Inductors A B -> A x :=
    match x return (Inductors A B -> A x) with
    | rat q => fun I => ind_rat I q
    | lim' f Hf => fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim I x a
    end
  with equiv_rect (x y : real) (e : Qpos) (xi : Requiv e x y) {struct xi}
    : forall I : Inductors A B, @B x y (real_rect x I) (real_rect y I) e xi :=
    match xi in equiv' e' x' y' return
      (forall I : Inductors A B,
        @B x' y' (real_rect x' I) (real_rect y' I) e' xi) with
    | equiv_rat_rat' q r e H => fun I => ind_rat_rat I q r e H
    | equiv_rat_lim' q f Hf e d d' He xi =>
      fun I =>
      let y := Build_Approximation f Hf in
      let b := Build_DApproximation A B y (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_rat_lim I q d d' e y b He xi (equiv_rect _ _ _ xi I)
    | equiv_lim_rat' f Hf r e d d' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim_rat I r d d' e x a He xi (equiv_rect _ _ _ xi I)
    | equiv_lim_lim' f Hf g Hg e d n e' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      let y := Build_Approximation g Hg in
      let b := Build_DApproximation A B y (fun e => real_rect (g e) I)
        (fun d e => equiv_rect (g d) (g e) _ (Hg d e) I) in
      ind_lim_lim I x y a b e d n e' He xi (equiv_rect _ _ _ xi I)
    end
  for equiv_rect x y e xi I.

Definition approx_rect (I : Inductors A B) (x : Approximation)
  : DApproximation A B x
  := Build_DApproximation A B x (fun e => real_rect I (x e))
      (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)).

Variable I : Inductors A B.

Definition real_rect_rat q : real_rect I (rat q) = ind_rat I q
  := idpath.

Definition real_rect_lim x : real_rect I (lim x) = ind_lim I x (approx_rect I x)
  := idpath.

End induction.

End VarSec.

End Cauchy.

