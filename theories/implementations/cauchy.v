Require Import
  HoTT.Types.Universe
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

Coercion trunctype_type : TruncType >-> Sortclass.

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

Instance qpos_plus_comm : Commutative (@plus Q+ _).
Proof.
hnf. intros.
apply pos_eq. change (' x + ' y = ' y + ' x).
apply plus_comm.
Qed.

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

Definition equiv_rect0 (P : forall e u v, Requiv Q e u v -> Type)
  `{forall e u v xi, IsHProp (P e u v xi)}
  (val_rat_rat : forall q r e He, P _ _ _ (equiv_rat_rat Q q r e He))
  (val_rat_lim : forall q (y : Approximation Q) e d d' He xi,
    P d' (rat q) (y d) xi ->
    P e (rat q) (lim y) (equiv_rat_lim Q q y e d d' He xi))
  (val_lim_rat : forall (x : Approximation Q) r e d d' He xi,
    P d' (x d) (rat r) xi ->
    P e (lim x) (rat r) (equiv_lim_rat Q x r e d d' He xi))
  (val_lim_lim : forall (x y : Approximation Q) e d n e' He xi,
    P e' (x d) (y n) xi ->
    P e (lim x) (lim y) (equiv_lim_lim Q x y e d n e' He xi))
  : forall e u v xi, P e u v xi.
Proof.
intros e u v;revert u v e.
apply (equiv_rect Q (fun _ => Unit) (fun x y _ _ e xi => P e x y xi)).
split;auto.
intros. apply path_ishprop. 
Defined.

Definition equiv_rec0 (P : Q+ -> real Q -> real Q -> Type)
  `{forall e u v, IsHProp (P e u v)}
  := equiv_rect0 (fun e u v _ => P e u v).

Lemma equiv_symm : forall e, Symmetric (Requiv Q e).
Proof.
red. apply (equiv_rec0 _).
- intros q r e He. apply equiv_rat_rat.
  split;apply flip_lt_negate;rewrite <-negate_swap_r,?involutive;apply He.
- intros q y e d d' He _ xi.
  apply equiv_lim_rat with d d';trivial.
- intros x r e d d' He _ xi.
  apply equiv_rat_lim with d d';trivial.
- intros x y e d n e' He _ xi.
  apply equiv_lim_lim with n d e';trivial.
  rewrite (commutativity (f:=plus) n d).
  trivial.
Qed.

Lemma equiv_symm_rw : forall e u v, Requiv Q e u v = Requiv Q e v u.
Proof.
intros. apply path_universe_uncurried.
apply equiv_iff_hprop_uncurried.
split;apply equiv_symm.
Qed.

Section mutual_recursion.

Record Recursors (A : Type) (B : Q+ -> A -> A -> Type) :=
  { rec_rat : Q -> A
  ; rec_lim : Approximation Q ->
      forall val_ind : Q+ -> A,
      (forall d e, B (d + e) (val_ind d) (val_ind e)) -> A
  ; rec_separated : forall x y, (forall e, B e x y) -> x = y
  ; rec_hprop : forall e x y, IsHProp (B e x y)
  ; rec_rat_rat : forall q r e, - ' e < q - r < ' e -> B e (rec_rat q) (rec_rat r)
  ; rec_rat_lim : forall q d d' e (y : Approximation Q) (b : Q+ -> A)
      (Eb : forall d e, B (d + e) (b d) (b e)),
      e = d + d' -> Requiv Q d' (rat q) (y d) ->
      B d' (rec_rat q) (b d) ->
      B e (rec_rat q) (rec_lim y b Eb)
  ; rec_lim_rat : forall r d d' e (x : Approximation Q) (a : Q+ -> A)
      (Ea : forall d e, B (d+e) (a d) (a e)),
      e = d + d' ->
      Requiv Q d' (x d) (rat r) ->
      B d' (a d) (rec_rat r) ->
      B e (rec_lim x a Ea) (rec_rat r)
  ; rec_lim_lim : forall (x y : Approximation Q) (a b : Q+ -> A)
      (Ea : forall d e, B (d + e) (a d) (a e))
      (Eb : forall d e, B (d + e) (b d) (b e))
      e d n e',
      e = d + n + e' ->
      Requiv Q e' (x d) (y n) ->
      B e' (a d) (b n) ->
      B e (rec_lim x a Ea) (rec_lim y b Eb) }.

Definition recursors_inductors : forall A B, Recursors A B ->
  Inductors Q (fun _ => A) (fun _ _ x y e _ => B e x y).
Proof.
intros A B I.
esplit. Unshelve. 7:exact (rec_rat _ _ I).
7:intros x [a Ea];revert x a Ea;simpl;exact (rec_lim _ _ I).
- intros;rewrite PathGroupoids.transport_const;apply (rec_separated _ _ I);trivial.
- exact (rec_rat_rat _ _ I).
- intros ????? [b Eb];simpl. apply rec_rat_lim.
- intros ????? [a Ea];simpl. apply rec_lim_rat.
- intros ?? [a Ea] [b Eb];simpl;apply rec_lim_lim.
- intros;apply (rec_hprop _ _ I).
Defined.

Definition real_rec A B (I : Recursors A B) : real Q -> A.
Proof.
apply (real_rect Q _ _ (recursors_inductors A B I)).
Defined.

Definition equiv_rec A B I
  : forall x y e, Requiv Q e x y -> B e (real_rec A B I x) (real_rec A B I y)
  := (equiv_rect Q) _ _ (recursors_inductors A B I).

End mutual_recursion.

Class Closeness (A : Type) := close : Q+ -> relation A.

Instance Q_close : Closeness Q := fun e q r => - ' e < q - r < ' e.
Instance R_close : Closeness (real Q) := Requiv Q.

Class Lipschitz `{Closeness A} `{Closeness B} (f : A -> B)
  := lipschitz : exists L : Q+, forall e x y, close e x y ->
    close (L * e) (f x) (f y).

Instance Qpos_mult_assoc : Associative (@mult Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply mult_assoc.
Qed.

Instance lipschitz_compose `{Closeness A} `{Closeness B} `{Closeness C}
  (g : B -> C) {Eg : Lipschitz g} (f : A -> B) {Ef : Lipschitz f}
  : Lipschitz (compose g f).
Proof.
hnf.
exists (Eg.1 * Ef.1).
intros ??? He.
unfold compose. apply Ef.2,Eg.2 in He.
pattern (Eg.1 * Ef.1 * e).
eapply transport;[|exact He].
apply Qpos_mult_assoc.
Defined.

Lemma Qpos_mult_1_l : forall e : Q+, 1 * e = e.
Proof.
intros;apply pos_eq;apply mult_1_l.
Qed.

Instance rat_lipschitz : Lipschitz rat.
Proof.
hnf. exists 1.
intros e x y. rewrite Qpos_mult_1_l.
apply equiv_rat_rat.
Qed.

Lemma pos_recip_through_plus : forall a b c : Q+,
  a + b = c * (a / c + b / c).
Proof.
intros. path_via ((a + b) * (c / c)).
- rewrite pos_recip_r;apply pos_eq,symmetry,mult_1_r.
- apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma pos_unconjugate : forall a b : Q+, a * b / a = b.
Proof.
intros. path_via (a / a * b).
- apply pos_eq;ring_tac.ring_with_nat.
- rewrite pos_recip_r;apply Qpos_mult_1_l.
Qed.

Lemma separate_mult : forall l u v, (forall e, Requiv Q (l * e) u v) -> u = v.
Proof.
intros l x y E. apply equiv_path.
intros. assert (Hrw : e = l * (e / l)).
+ path_via ((l / l) * e).
   * rewrite pos_recip_r. apply symmetry,Qpos_mult_1_l.
   * apply pos_eq. ring_tac.ring_with_nat.
+ rewrite Hrw;apply E.
Qed.

Lemma lipschitz_extend_rat_lim (f : Q -> Q) {Ef : Lipschitz f} :
  ∀ (q : Q) (d d' e : Q+) (y : Approximation Q) (b : Q+ → real Q)
  (Eb : ∀ d0 e0 : Q+, Requiv Q (Ef.1 * (d0 + e0)) (b d0) (b e0)) Eequiv,
  e = d + d'
  → Requiv Q d' (rat q) (y d)
  → Requiv Q (Ef.1 * d') ((rat ∘ f) q) (b d)
  → Requiv Q (Ef.1 * e) ((rat ∘ f) q)
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / Ef.1);
         approx_equiv := Eequiv |}).
Proof.
simpl. intros ???????? He xi IH.
apply equiv_rat_lim with (Ef.1 * d) (Ef.1 * d').
+ rewrite He;apply pos_eq;ring_tac.ring_with_nat.
+ simpl. rewrite (pos_unconjugate Ef.1 d). apply IH.
Qed.

Lemma lipschitz_extend_lim_lim (f : Q -> Q) {Ef : Lipschitz f} :
  ∀ (x y : Approximation Q) (a b : Q+ → real Q)
  (Ea : ∀ d e : Q+, Requiv Q (Ef.1 * (d + e)) (a d) (a e))
  (Eb : ∀ d e : Q+, Requiv Q (Ef.1 * (d + e)) (b d) (b e)) (e d n e' : Q+)
  Eequiv1 Eequiv2,
  e = d + n + e'
  → Requiv Q e' (x d) (y n)
  → Requiv Q (Ef.1 * e') (a d) (b n)
  → Requiv Q (Ef.1 * e)
      (lim
         {|
         approximate := λ e0 : Q+, a (e0 / Ef.1);
         approx_equiv := Eequiv1 |})
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / Ef.1);
         approx_equiv := Eequiv2 |}).
Proof.
intros ???????????? He xi IH;simpl.
apply equiv_lim_lim with (Ef.1 * d) (Ef.1 * n) (Ef.1 * e').
+ rewrite He;apply pos_eq;ring_tac.ring_with_nat.
+ simpl. rewrite 2!pos_unconjugate. apply IH.
Qed.

Lemma lipschitz_extend_lim (f : Q -> Q) {Ef : Lipschitz f} :
  forall (a : Q+ → real Q)
  (Ea : ∀ d e : Q+, Requiv Q (Ef.1 * (d + e)) (a d) (a e)),
  ∀ d e : Q+, Requiv Q (d + e) (a (d / Ef.1)) (a (e / Ef.1)).
Proof.
intros. pattern (d+e);eapply transport.
apply symmetry, (pos_recip_through_plus d e Ef.1).
apply Ea.
Qed.

Definition lipshitz_extend_recursor (f : Q -> Q) {Ef : Lipschitz f}
  : Recursors (real Q) (fun e x y => Requiv Q (Ef.1 * e) x y).
Proof.
esplit. Unshelve.
Focus 7.
- exact (compose rat f).
Focus 7.
- intros _ a Ea.
  apply lim. exists (fun e => a (e / Ef.1)).
  apply lipschitz_extend_lim. trivial.
- apply separate_mult.
- apply _.
- intros ??? He. apply equiv_rat_rat.
  apply Ef.2,He.
- intros ????????;apply lipschitz_extend_rat_lim;trivial.
- simpl;intros ??????? He xi IH.
  apply equiv_symm in xi;apply equiv_symm in IH.
  apply equiv_symm;revert He xi IH;apply lipschitz_extend_rat_lim;trivial.
- simpl. intros ??????????;apply lipschitz_extend_lim_lim;trivial.
Defined.

Definition lipschitz_extend (f : Q -> Q) {Ef : Lipschitz f}
  : real Q -> real Q
  := real_rec (real Q) (fun e x y => Requiv Q (Ef.1 * e) x y)
    (lipshitz_extend_recursor f).

Lemma lipschitz_extend_lipshitz_pr (f : Q -> Q) {Ef : Lipschitz f}
  : ∀ (e : Q+) (x y : real Q), close e x y →
    close (Ef.1 * e) (lipschitz_extend f x) (lipschitz_extend f y).
Proof.
intros ???;apply (equiv_rec _ _ (lipshitz_extend_recursor f)).
Qed.

Instance lipschitz_extend_lipshitz (f : Q -> Q) {Ef : Lipschitz f}
  : Lipschitz (lipschitz_extend f).
Proof.
exists Ef.1. apply lipschitz_extend_lipshitz_pr.
Defined.

Definition lipschitz_extend_rat (f : Q -> Q) {Ef : Lipschitz f}
  q : lipschitz_extend f (rat q) = rat (f q)
  := idpath.

Section Requiv_alt.

Let A := sigT (fun half : real Q -> Q+ -> hProp =>
  (forall u e, half u e <-> merely (exists d d', e = d + d' /\ half u d))
  /\ (forall u v n e, Requiv Q e u v ->
    ((half u n -> half v (n+e)) /\ (half v n -> half v (n+e))))).

Let A_close e (R1 R2 : A)
  := forall u n, (R1.1 u n -> R2.1 u (e+n)) /\ (R2.1 u n -> R1.1 u (e+n)).

Let C := sigT (fun R : Q+ -> hProp =>
    forall e, R e <-> merely (exists d d', e = d + d' /\ R d)).

Let C_close e (R1 R2 : C)
  := forall n, (R1.1 n -> R2.1 (e+n)) /\ (R2.1 n -> R1.1 (e+n)).

Lemma A_separated : forall u v, (forall e, A_close e u v) -> u = v.
Proof.
intros u v E. eapply Sigma.path_sigma. Unshelve.
apply path_ishprop.
apply path_forall. intro x. apply path_forall. intro e.
apply TruncType.path_iff_hprop_uncurried.
unfold A_close in E.
split;intros E'.
+ generalize (fst (fst u.2 _ _) E').
  apply (Trunc_ind _).
  intros [d [d' [He Ed]]].
  rewrite He. rewrite qpos_plus_comm. apply (fst (E _ _ _)).
  trivial.
+ generalize (fst (fst v.2 _ _) E').
  apply (Trunc_ind _).
  intros [d [d' [He Ed]]].
  rewrite He. rewrite qpos_plus_comm. apply (snd (E _ _ _)).
  trivial.
Qed.

Instance A_close_hprop : forall e u v, IsHProp (A_close e u v).
Proof.
unfold A_close. intros. apply _.
Qed.

Lemma Qclose_rounded : ∀ (q r : Q) e, close e q r ↔
  merely (∃ d d' : Q+, e = d + d' ∧ close d q r).
Proof. Admitted.

Definition Requiv_alt_rat_rat (q r : Q) : C.
Proof.
exists (fun e => BuildhProp (close e q r)).
simpl. apply Qclose_rounded.
Defined.

Lemma rat_lim_rounded_step :
  ∀ val_ind : Q+ → C, (∀ d e : Q+, C_close (d + e) (val_ind d) (val_ind e)) ->
  ∀ e : Q+,
  merely (∃ d d' : Q+, e = d + d' ∧ (val_ind d).1 d')
  ↔ merely (∃ d d' : Q+,
     e = d + d' ∧ merely (∃ d0 d'0 : Q+, d = d0 + d'0 ∧ (val_ind d0).1 d'0)).
Proof. Admitted.

Definition Requiv_alt_rat_lim
  : ∀ val_ind : Q+ → C, (∀ d e : Q+, C_close (d + e) (val_ind d) (val_ind e)) →
  C.
Proof.
intros val_ind IH.
exists (fun e => merely (exists d d', e = d + d' /\ (val_ind d).1 d')).
apply rat_lim_rounded_step. trivial.
Defined.

Lemma C_separated : ∀ x y : C, (∀ e : Q+, C_close e x y) → x = y.
Proof.
intros x y E.
unfold C,C_close in *;clear A A_close C C_close.
simple refine (Sigma.path_sigma _ _ _ _ _);[|apply path_ishprop].
apply path_forall;intros e.
apply TruncType.path_iff_hprop_uncurried.
split;intros E'.
- generalize (fst (x.2 _) E').
  apply (Trunc_ind _).
  intros [d [d' [He Ed]]].
  rewrite He,qpos_plus_comm.
  apply (fst (E _ _)). trivial.
- generalize (fst (y.2 _) E').
  apply (Trunc_ind _).
  intros [d [d' [He Ed]]].
  rewrite He,qpos_plus_comm.
  apply (snd (E _ _)). trivial.
Qed.

Definition Requiv_alt : Q+ -> real Q -> real Q -> Type.
Proof.
transparent assert (V : (real Q -> A)).
Focus 2. - intros e x y;exact ((V x).1 y e).
apply (real_rec A A_close).
simple refine (Build_Recursors A A_close _ _ A_separated _ _ _ _ _).
- intros q.
  transparent assert (Requiv_q : (real Q -> C)).
  + apply (real_rec C C_close).
    simple refine (Build_Recursors C C_close _ _ C_separated _ _ _ _ _).
    * intros r. apply (Requiv_alt_rat_rat q r).
    * intros _. apply Requiv_alt_rat_lim.
    * unfold C_close. apply _.
    * unfold Requiv_alt_rat_rat.
      red;simpl. intros r1 r2 e Hr n.
      admit. (* triangular equality for Q *)
    * unfold C_close;simpl.
Defined.

End Requiv_alt.

