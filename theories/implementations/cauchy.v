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
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals.

Module Export Cauchy.

Section VarSec.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals Q}.

Record Qpos := mkQpos { pos : Q; is_pos : 0 < pos }.
Notation "Q+" := Qpos.

Instance : Cast Qpos Q := pos.

Lemma Qpos_plus_pr : forall a b : Qpos, 0 < 'a + 'b.
Proof.
intros.
apply semirings.pos_plus_compat;apply is_pos.
Qed.

Instance Qpos_plus : Plus Qpos := fun a b => mkQpos _ (Qpos_plus_pr a b).

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
  {x y : real} {e : Qpos} (xi : Requiv e x y),
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
      (fun d e => equiv_rect I (approx_equiv x d e)).

Variable I : Inductors A B.

Definition real_rect_rat q : real_rect I (rat q) = ind_rat I q
  := idpath.

Definition real_rect_lim x : real_rect I (lim x) = ind_lim I x (approx_rect I x)
  := idpath.

Definition equiv_rect_rat_rat q r e E : equiv_rect I (equiv_rat_rat q r e E)
  = ind_rat_rat I q r e E
  := idpath.

Definition equiv_rect_rat_lim q y e d d' He xi
  : equiv_rect I (equiv_rat_lim q y e d d' He xi)
  = ind_rat_lim I q d d' e y (approx_rect I y) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_rat x r e d d' He xi
  : equiv_rect I (equiv_lim_rat x r e d d' He xi)
  = ind_lim_rat I r d d' e x (approx_rect I x) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_lim x y e d n e' He xi
  : equiv_rect I (equiv_lim_lim x y e d n e' He xi)
  = ind_lim_lim I x y (approx_rect I x) (approx_rect I y)
                  e d n e' He xi (equiv_rect I xi)
  := idpath.

End induction.

End VarSec.

End Cauchy.

Arguments equiv_path {Q _ _ _ _ _ _ _ _ _ _ _} u v {_}.

Section contents.
Context `{Funext} `{Universe.Univalence}.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals Q} `{!TrivialApart Q} `{DecidablePaths Q}.

Notation "Q+" := (Qpos Q).

Instance : Cast (Qpos Q) Q := pos Q.

Instance pos_is_pos : forall q : Qpos Q, PropHolds (0 < ' q)
  := is_pos Q.

Lemma pos_eq : forall a b : Qpos Q, @paths Q (' a) (' b) -> a = b.
Proof.
intros [a Ea] [b Eb] E.
change (a = b) in E.
destruct E;apply ap;apply path_ishprop.
Qed.

Existing Instance Qpos_plus.

Instance Qpos_one : One Q+.
Proof.
exists 1. solve_propholds.
Defined.

Instance Qpos_mult : Mult Q+.
Proof.
intros a b;exists (' a * ' b).
solve_propholds.
Defined.

Let rat := rat Q.
Let lim := lim Q.

Definition real_rect0 (A : real Q -> Type) (val_rat : forall q, A (rat q))
  (val_lim : forall (x : Approximation Q) (a : forall e, A (x e)), A (lim x))
  (val_respects : forall u v (h : forall e, Requiv Q e u v) (a : A u) (b : A v),
    equiv_path u v # a = b)
  : forall x, A x.
Proof.
apply (real_rect Q A (fun _ _ _ _ _ _ => Unit)).
split;auto;try apply _.
intros. apply val_lim. intros;apply a.
Defined.

Definition real_ind0 (A : real Q -> Type) `{forall q, IsHProp (A q)}
  (A_rat : forall q, A (rat q))
  (A_lim : forall (x : Approximation Q) (a : forall e, A (x e)), A (lim x))
  : forall x, A x.
Proof.
apply real_rect0;auto.
intros. apply path_ishprop.
Qed.

Instance pos_recip : DecRecip Q+.
Proof.
intros e. exists (/ ' e).
solve_propholds.
Defined.

Instance pos_of_nat : Cast nat Q+.
Proof.
intros n. destruct n as [|k].
- exists 1;solve_propholds.
- exists (naturals_to_semiring nat Q (S k)).
  induction k as [|k Ik].
  + change (0 < 1). solve_propholds.
  + change (0 < 1 + naturals_to_semiring nat Q (S k)).
    set (K := naturals_to_semiring nat Q (S k)) in *;clearbody K.
    solve_propholds.
Defined.

Lemma pos_recip_r : forall e : Q+, e / e = 1.
Proof.
intros;apply pos_eq.
unfold dec_recip,cast,pos_recip;simpl.
change (' e / ' e = 1). apply dec_recip_inverse.
apply lt_ne_flip. solve_propholds.
Qed.

Lemma pos_recip_r' : forall e : Q+, @paths Q (' e / ' e) 1.
Proof.
intros. change (' (e / e) = 1). rewrite pos_recip_r. reflexivity.
Qed.

Lemma pos_mult_1_r : forall e : Q+, e * 1 = e.
Proof.
intros;apply pos_eq. apply mult_1_r.
Qed.

Lemma pos_split2 : forall e : Qpos Q, e = e / 2 + e / 2.
Proof.
intros.
path_via (e * (2 / 2)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (2 / 2) = ' e / 2 + ' e / 2).
  ring_tac.ring_with_nat.
Qed.

Lemma pos_split3 : forall e : Qpos Q, e = e / 3 + e / 3 + e / 3.
Proof.
intros.
path_via (e * (3 / 3)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (3 / 3) = ' e / 3 + ' e / 3 + ' e / 3).
  ring_tac.ring_with_nat.
Qed.

Instance : forall e, Reflexive (Requiv Q e).
Proof.
red. intros e u;revert u e.
apply (real_ind0 (fun u => forall e, _)).
- intros. apply equiv_rat_rat. rewrite plus_negate_r.
  split;[apply rings.flip_pos_negate|];apply is_pos.
- intros. eapply equiv_lim_lim;[apply pos_split3|].
  auto.
Qed.

Global Instance real_isset : IsHSet (real Q).
Proof.
eapply @HSet.isset_hrel_subpaths.
3:apply equiv_path.
- red. intros;reflexivity.
- apply _.
Qed.

Definition const_approx : real Q -> Approximation Q.
Proof.
intros x;exists (fun _ => x).
intros;reflexivity.
Defined.

Lemma lim_cons : forall x, lim (const_approx x) = x.
Proof.
apply (real_ind0 _).
- intros. apply equiv_path.
  intros. eapply equiv_lim_rat;[apply pos_split2|].
  simpl. reflexivity.
- intros x Hx. apply equiv_path. intros.
  eapply equiv_lim_lim;[|
  simpl; rewrite <-Hx;
  eapply equiv_lim_lim;[|simpl;reflexivity]].
  + path_via (e / 5 + e / 5 + (e * 3 / 5)).
    path_via (e * (5 / 5)).
    * rewrite pos_recip_r,pos_mult_1_r;reflexivity.
    * apply pos_eq.
      change (' e * (5 / 5) = ' e / 5 + ' e / 5 + ' e * 3 / 5).
      ring_tac.ring_with_nat.
  + path_via (e / 5 + e / 5 + e / 5).
    apply pos_eq.
    unfold cast,mult,Qpos_mult;simpl.
    unfold cast,dec_recip;simpl. ring_tac.ring_with_nat.
Qed.

Lemma lim_epi : epi.isepi lim.
Proof.
apply epi.issurj_isepi.
apply BuildIsSurjection.
intros. apply tr. exists (const_approx b).
apply lim_cons.
Qed.

End contents.
