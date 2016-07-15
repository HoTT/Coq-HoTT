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
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices.

Local Set Universe Minimization ToSet.

Coercion trunctype_type : TruncType >-> Sortclass.

Class Closeness@{k i} (R:Type@{k}) (A : Type@{i}) := close : R -> relation@{i i} A.
Arguments close {R A _} _ _ _.

Class Separated R A `{Closeness R A}
  := separated : forall x y, (forall e, close e x y) -> x = y :> A.

Class Triangular R `{Plus R} A `{Closeness R A}
  := triangular : forall {u v w e d}, close e u v -> close d v w ->
  close (e+d) u w.

Class NonExpanding `{Closeness R A} `{Closeness R B} (f : A -> B)
  := non_expanding : forall e x y, close e x y -> close e (f x) (f y).
Arguments non_expanding {R A _ B _} f {_ e x y} _.

Class Lipschitz `{Mult R} `{Closeness R A} `{Closeness R B} (f : A -> B) (L : R)
  := lipschitz : forall e x y, close e x y -> close (L * e) (f x) (f y).
Arguments lipschitz {R _ A _ B _} f L {_ e x y} _.

Class Continuous@{UR UA UB}
  {R:Type@{UR} } {A:Type@{UA} } `{Closeness R A}
  {B:Type@{UB} } `{Closeness R B} (f : A -> B)
  := continuous : forall u e, merely@{Ularge} (sigT@{UR Ularge}
    (fun d => forall v, close d u v ->
    close e (f u) (f v))).
Arguments continuous {R A _ B _} f {_} _ _.

Class UniformlyContinuous@{UR UA UB}
  {R:Type@{UR} } {A:Type@{UA} } `{Closeness R A}
  {B:Type@{UB} } `{Closeness R B} (f : A -> B)
  := uniformly_continuous
    : forall e, merely@{Ularge} (sigT@{UR Ularge}
    (fun d => forall u v, close d u v -> close e (f u) (f v))).
Arguments uniformly_continuous {R A _ B _} f {_} _.

Module Qpos.

Section VarSec.
Context `{Funext} `{Universe.Univalence}.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}
  `{!TrivialApart Q} `{DecidablePaths Q}
  {Qmeet : Meet Q} {Qjoin : Join Q} `{!LatticeOrder Ale}
  `{!TotalRelation (@le Q _)} `{!Abs Q}.

Record Qpos@{} : Type@{UQ} := mkQpos { pos : Q; is_pos : 0 < pos }.
Notation "Q+" := Qpos.

Global Instance Qpos_Q@{} : Cast Qpos Q := pos.
Arguments Qpos_Q /.

Global Instance Q_close@{} : Closeness Q+ Q := fun e q r => - ' e < q - r < ' e.

Lemma Qpos_plus_pr@{} : forall a b : Qpos, 0 < 'a + 'b.
Proof.
intros.
apply semirings.pos_plus_compat;apply is_pos.
Qed.

Global Instance Qpos_plus@{} : Plus Qpos := fun a b => mkQpos _ (Qpos_plus_pr a b).

Global Instance pos_is_pos@{} : forall q : Q+, PropHolds (0 < ' q)
  := is_pos.

Lemma pos_eq@{} : forall a b : Q+, @paths Q (' a) (' b) -> a = b.
Proof.
intros [a Ea] [b Eb] E.
change (a = b) in E.
destruct E;apply ap;apply path_ishprop.
Qed.

Global Instance Qpos_one@{} : One Q+.
Proof.
exists 1. apply lt_0_1.
Defined.

Global Instance Qpos_mult@{} : Mult Q+.
Proof.
intros a b;exists (' a * ' b).
solve_propholds.
Defined.

Global Instance qpos_plus_comm@{} : Commutative (@plus Q+ _).
Proof.
hnf. intros.
apply pos_eq. change (' x + ' y = ' y + ' x).
apply plus_comm.
Qed.

Global Instance qpos_mult_comm@{} : Commutative (@mult Q+ _).
Proof.
hnf;intros;apply pos_eq,mult_comm.
Qed.

Global Instance pos_recip@{} : DecRecip Q+.
Proof.
intros e. exists (/ ' e).
apply pos_dec_recip_compat.
solve_propholds.
Defined.

Global Instance pos_of_nat@{} : Cast nat Q+.
Proof.
intros n. destruct n as [|k].
- exists 1;apply lt_0_1.
- exists (naturals_to_semiring nat Q (S k)).
  induction k as [|k Ik].
  + change (0 < 1). apply lt_0_1.
  + change (0 < 1 + naturals_to_semiring nat Q (S k)).
    set (K := naturals_to_semiring nat Q (S k)) in *;clearbody K.
    apply pos_plus_compat.
    apply lt_0_1.
    trivial.
Defined.

Lemma pos_recip_r@{} : forall e : Q+, e / e = 1.
Proof.
intros;apply pos_eq.
unfold dec_recip,cast,pos_recip;simpl.
change (' e / ' e = 1). apply dec_recip_inverse.
apply lt_ne_flip. solve_propholds.
Qed.

Lemma pos_recip_r'@{} : forall e : Q+, @paths Q (' e / ' e) 1.
Proof.
intros. change (' (e / e) = 1). rewrite pos_recip_r. reflexivity.
Qed.

Lemma pos_mult_1_r@{} : forall e : Q+, e * 1 = e.
Proof.
intros;apply pos_eq. apply mult_1_r.
Qed.

Lemma pos_split2@{} : forall e : Q+, e = e / 2 + e / 2.
Proof.
intros.
path_via (e * (2 / 2)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (2 / 2) = ' e / 2 + ' e / 2).
  ring_tac.ring_with_nat.
Qed.

Lemma pos_split3@{} : forall e : Q+, e = e / 3 + e / 3 + e / 3.
Proof.
intros.
path_via (e * (3 / 3)).
- rewrite pos_recip_r,pos_mult_1_r;reflexivity.
- apply pos_eq. change (' e * (3 / 3) = ' e / 3 + ' e / 3 + ' e / 3).
  ring_tac.ring_with_nat.
Qed.

Global Instance Qpos_mult_assoc@{} : Associative (@mult Q+ _).
Proof.
hnf.
intros;apply pos_eq.
apply mult_assoc.
Qed.

Global Instance Qpos_mult_1_l@{} : LeftIdentity (@mult Q+ _) 1.
Proof.
hnf;intros;apply pos_eq;apply mult_1_l.
Qed.

Lemma pos_recip_through_plus@{} : forall a b c : Q+,
  a + b = c * (a / c + b / c).
Proof.
intros. path_via ((a + b) * (c / c)).
- rewrite pos_recip_r;apply pos_eq,symmetry,mult_1_r.
- apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma pos_unconjugate@{} : forall a b : Q+, a * b / a = b.
Proof.
intros. path_via (a / a * b).
- apply pos_eq;ring_tac.ring_with_nat.
- rewrite pos_recip_r;apply Qpos_mult_1_l.
Qed.

End VarSec.

End Qpos.
Import Qpos.

Section closeness.
Universe UR UA.
Context {R:Type@{UR} }
  `{Rmult : Mult R} {Rone :  One R} `{LeftIdentity R R Rmult Rone}
  {A:Type@{UA} } `{Closeness R A}.

Global Instance id_nonexpanding : NonExpanding (@id A).
Proof.
hnf;trivial.
Qed.

Universe UB.
Context {B:Type@{UB} } `{Closeness R B} (f : A -> B).

Lemma nonexpanding_lipschitz' `{!NonExpanding f}
  : Lipschitz f 1.
Proof.
red. intro;rewrite left_identity;apply non_expanding,_.
Qed.

Definition nonexpanding_lipschitz@{} `{!NonExpanding f}
  : Lipschitz f 1
  := nonexpanding_lipschitz'@{Ularge}.
Global Existing Instance nonexpanding_lipschitz.


Lemma lipschitz_nonexpanding@{} `{!Lipschitz f 1} : NonExpanding f.
Proof.
red. intros e x y E;rewrite <-(left_identity e). apply (lipschitz f 1 E).
Qed.

Global Instance const_nonexpanding@{} `{forall e, Reflexive (close (A:=B) e)}
  (b : B) : NonExpanding (fun _ : A => b).
Proof.
hnf. intros;reflexivity.
Qed.

End closeness.

Section closeness_qpos.
Context `{Funext} `{Universe.Univalence}.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}
  `{!TrivialApart Q} `{DecidablePaths Q}
  {Qmeet : Meet Q} {Qjoin : Join Q} `{!LatticeOrder Ale}
  `{!TotalRelation (@le Q _)} `{!Abs Q}.
Notation "Q+" := (Qpos.Qpos Q).
Universe UA.
Context {A:Type@{UA} } `{Closeness Q+ A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness Q+ B} (f : A -> B).

Lemma uniformly_continuous_continuous@{}
  `{!UniformlyContinuous@{UQ UA UB} f} : Continuous f.
Proof.
intros u e. generalize (uniformly_continuous f e). apply (Trunc_ind _).
intros d;apply tr;exists d.1;apply d.2.
Qed.
Global Existing Instance uniformly_continuous_continuous.

Lemma lipschitz_uniformly_continuous@{} (L:Q+) `{!Lipschitz f L}
  : UniformlyContinuous@{UQ UA UB} f.
Proof.
red.
intros e;apply tr;exists (e / L).
intros u v E.
apply(lipschitz f L) in E.
rewrite Qpos_mult_assoc,pos_unconjugate in E. trivial.
Qed.
Global Existing Instance lipschitz_uniformly_continuous.

Definition lipschitz_continuous@{} (L:Q+) `{!Lipschitz f L}
  : Continuous@{UQ UA UB} f
  := _.

Definition nonexpanding_continuous@{} `{!NonExpanding f}
  : Continuous@{UQ UA UB} f
  := _.

End closeness_qpos.

Section compositions.
Universe UR UA.
Context {R:Type@{UR} }
  `{Rmult : Mult R} {Rone :  One R} `{LeftIdentity R R Rmult Rone}
  {A:Type@{UA} } `{Closeness R A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness R B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness R C} (g : B -> C) (f : A -> B).

Global Instance nonexpanding_compose@{}
  {Eg : NonExpanding g} {Ef : NonExpanding f}
  : NonExpanding (compose g f).
Proof.
hnf. intros e x y xi;exact (non_expanding g (non_expanding f xi)).
Qed.

Global Instance lipschitz_compose@{} `{!Associative Rmult}
  Lg {Eg : Lipschitz g Lg} Lf {Ef : Lipschitz f Lf}
  : Lipschitz (compose g f) (Lg * Lf).
Proof.
intros ??? He.
unfold compose;apply Ef,Eg in He.
pattern (Lg * Lf * e).
eapply transport;[|exact He].
apply associativity.
Qed.

Lemma lipschitz_compose_nonexpanding_r'
  `{!Associative Rmult} `{!Commutative Rmult}
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L),commutativity. apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_r@{}
  `{!Associative Rmult} `{!Commutative Rmult}
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_r'@{Ularge} L.

Lemma lipschitz_compose_nonexpanding_l'
  `{!Associative Rmult}
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L). apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_l@{}
  `{!Associative Rmult}
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_l'@{Ularge} L.

Global Instance continuous_compose@{} {Eg : Continuous g} {Ef : Continuous f}
  : Continuous (compose g f).
Proof.
intros u e.
apply (merely_destruct (continuous g (f u) e)).
intros [d E].
apply (merely_destruct (continuous f u d)).
intros [d' E'].
apply tr;exists d';intros v xi.
apply E,E',xi.
Qed.

End compositions.

Section interval.
Universe UA UALE.
Context {A:Type@{UA} } {Ale : Le@{UA UALE} A}.

Definition Interval a b := sigT (fun x : A => a <= x /\ x <= b).

Section interval_restrict.
Context `{IsHSet A} {Ameet : Meet A} {Ajoin : Join A}
  `{!LatticeOrder@{UA UALE} Ale}.

Definition Interval_restrict@{} (a b : A) (E : a <= b) : A -> Interval a b.
Proof.
intros x.
exists (join a (meet x b)).
split.
- apply join_ub_l.
- apply join_le.
  + exact E.
  + apply meet_lb_r.
Defined.

Lemma Interval_restrict_pr : forall a b E x (E': a <= x /\ x <= b),
  Interval_restrict a b E x = existT _ x E'.
Proof.
intros a b E x E'.
unfold Interval_restrict.
apply Sigma.path_sigma_hprop.
simpl. rewrite meet_l;[apply join_r|];apply E'.
Qed.

End interval_restrict.

Universe UR.
Context {R:Type@{UR} } `{Rmult : Mult R} {Rone :  One R}
  `{LeftIdentity R R Rmult Rone}
  `{Closeness R A}.

Global Instance Interval_close (a b : A) : Closeness R (Interval a b)
  := fun e x y => close e x.1 y.1.
Arguments Interval_close _ _ _ _ _ /.

Global Instance interval_project_nonexpanding (a b : A)
  : NonExpanding (fun x : Interval a b => x.1).
Proof.
intros e x y xi;exact xi.
Qed.

End interval.


Module Export Cauchy.

Section VarSec.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}.

Notation "Q+" := (Qpos.Qpos Q).

Private Inductive real@{} : Type@{UQ} :=
  | rat : Q -> real
  | lim' : forall (f : Q+ -> real),
    (forall d e : Q+, close (d+e) (f d) (f e)) -> real

with equiv@{} : Closeness@{UQ UQ} Q+ real :=
  | equiv_rat_rat : forall (q r : Q) (e : Q+),
      close e q r ->
      close e (rat q) (rat r)
  | equiv_rat_lim' : forall q y Hy (e d d' : Q+),
      e = d + d' ->
      close d' (rat q) (y d) ->
      close e (rat q) (lim' y Hy)
  | equiv_lim'_rat : forall x Hx r (e d d' : Q+),
      e = d + d' ->
      close d' (x d) (rat r) ->
      close e (lim' x Hx) (rat r)
  | equiv_lim'_lim' : forall x Hx y Hy (e d n e' : Q+),
      e = d + n + e' ->
      close e' (x d) (y n) ->
      close e (lim' x Hx) (lim' y Hy)
.

Global Existing Instance equiv.

Axiom equiv_path@{} : Separated Q+ real.
Axiom equiv_hprop@{} : forall e (u v : real), IsHProp (close e u v).
Global Existing Instance equiv_path.
Global Existing Instance equiv_hprop.

Record Approximation@{} :=
  { approximate :> Q+ -> real
  ; approx_equiv : forall d e, close (d+e) (approximate d) (approximate e) }.

Definition lim@{} (x : Approximation) : real :=
  lim' x (fun _ _ => approx_equiv _ _ _).

Definition equiv_rat_lim@{} : forall q (y:Approximation) (e d d' : Q+),
  e = d + d' ->
  close d' (rat q) (y d) ->
  close e (rat q) (lim y).
Proof.
intros. eapply equiv_rat_lim';eauto.
Defined.

Definition equiv_lim_rat@{} : forall (x:Approximation) r (e d d' : Q+),
  e = d + d' ->
  close d' (x d) (rat r) ->
  close e (lim x) (rat r).
Proof.
intros;eapply equiv_lim'_rat;eauto.
Defined.

Definition equiv_lim_lim@{} : forall (x y : Approximation) (e d n e' : Q+),
  e = d + n + e' ->
  close e' (x d) (y n) ->
  close e (lim x) (lim y).
Proof.
intros;eapply equiv_lim'_lim';eauto.
Defined.

Record DApproximation@{UA UB} (A : real -> Type@{UA})
  (B : forall x y : real, A x -> A y -> forall e, close e x y -> Type@{UB})
  (x : Approximation) :=
  { dapproximation :> forall e, A (x e)
  ; dapproximation_correct :
    forall d e, B (x d) (x e) (dapproximation d) (dapproximation e) (d+e)
      (approx_equiv _ _ _) }.

Record Inductors@{UA UB} (A : real -> Type@{UA})
  (B : forall x y : real, A x -> A y -> forall e, close e x y -> Type@{UB}) :=
  { ind_rat : forall q, A (rat q)
  ; ind_lim : forall (x:Approximation) (a : DApproximation A B x),
    A (lim x)

  ; ind_path_A : forall u v (u_equiv_v : forall e, close e u v),
    forall (a : A u) (b : A v), (forall e, B u v a b e (u_equiv_v _)) ->
    equiv_path u v u_equiv_v # a = b

  ; ind_rat_rat : forall q r e (Hqr : close e q r),
      @B (rat q) (rat r) (ind_rat q) (ind_rat r) e (equiv_rat_rat _ _ _ Hqr)
  ; ind_rat_lim : forall q d d' e y (b : DApproximation A B y)
      (He : e = d + d')
      (xi : close d' (rat q) (y d)),
      B (rat q) (y d) (ind_rat q) (b d) d' xi ->
      @B (rat q) (lim y) (ind_rat q) (ind_lim y b) e
         (equiv_rat_lim _ _ _ _ _ He xi)
   ; ind_lim_rat : forall r d d' e x (a : DApproximation A B x)
      (He : e = d + d')
      (xi : close d' (x d) (rat r)),
      B (x d) (rat r) (a d) (ind_rat r) d' xi ->
      @B (lim x) (rat r) (ind_lim x a) (ind_rat r) e
         (equiv_lim_rat _ _ _ _ _ He xi)
   ; ind_lim_lim : forall x y (a : DApproximation A B x) (b : DApproximation A B y)
      e d n e' (He : e = d + n + e')
      (xi : close e' (x d) (y n)),
      B (x d) (y n) (a d) (b n) e' xi ->
      @B (lim x) (lim y) (ind_lim x a) (ind_lim y b) e
         (equiv_lim_lim _ _ _ _ _ _ He xi)

   ; ind_hprop_B : forall x y a b e xi, IsHProp (@B x y a b e xi) }.

Arguments ind_rat {_ _} _ _.
Arguments ind_lim {_ _} _ _ _.
Arguments ind_rat_rat {_ _} _ _ _ _ _.
Arguments ind_rat_lim {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_rat {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_lim {_ _} _ _ _ _ _ _ _ _ _ _ _ _.

Section induction.
Universe UA UB.
Variable A : real -> Type@{UA}.
Variable B : forall x y : real, A x -> A y -> forall e, close e x y -> Type@{UB}.

Definition real_rect@{} : Inductors A B -> forall x : real, A x :=
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

  with equiv_rect (x y : real) (e : Q+) (xi : close e x y) {struct xi}
    : forall I : Inductors A B, B x y (real_rect x I) (real_rect y I) e xi :=
    match xi in equiv e' x' y' return
      (forall I : Inductors A B,
        @B x' y' (real_rect x' I) (real_rect y' I) e' xi) with
    | equiv_rat_rat q r e H => fun I => ind_rat_rat I q r e H
    | equiv_rat_lim' q f Hf e d d' He xi =>
      fun I =>
      let y := Build_Approximation f Hf in
      let b := Build_DApproximation A B y (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_rat_lim I q d d' e y b He xi (equiv_rect _ _ _ xi I)
    | equiv_lim'_rat f Hf r e d d' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim_rat I r d d' e x a He xi (equiv_rect _ _ _ xi I)
    | equiv_lim'_lim' f Hf g Hg e d n e' He xi =>
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

Definition equiv_rect@{} : forall (I : Inductors A B)
  {x y : real} {e : Q+} (xi : close e x y),
  B x y (real_rect I x) (real_rect I y) e xi :=
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
  with equiv_rect (x y : real) (e : Q+) (xi : close e x y) {struct xi}
    : forall I : Inductors A B, @B x y (real_rect x I) (real_rect y I) e xi :=
    match xi in equiv e' x' y' return
      (forall I : Inductors A B,
        B x' y' (real_rect x' I) (real_rect y' I) e' xi) with
    | equiv_rat_rat q r e H => fun I => ind_rat_rat I q r e H
    | equiv_rat_lim' q f Hf e d d' He xi =>
      fun I =>
      let y := Build_Approximation f Hf in
      let b := Build_DApproximation A B y (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_rat_lim I q d d' e y b He xi (equiv_rect _ _ _ xi I)
    | equiv_lim'_rat f Hf r e d d' He xi =>
      fun I =>
      let x := Build_Approximation f Hf in
      let a := Build_DApproximation A B x (fun e => real_rect (f e) I)
        (fun d e => equiv_rect (f d) (f e) _ (Hf d e) I) in
      ind_lim_rat I r d d' e x a He xi (equiv_rect _ _ _ xi I)
    | equiv_lim'_lim' f Hf g Hg e d n e' He xi =>
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

Definition approx_rect@{} (I : Inductors A B) (x : Approximation)
  : DApproximation A B x
  := Build_DApproximation A B x (fun e => real_rect I (x e))
      (fun d e => equiv_rect I (approx_equiv x d e)).

Variable I : Inductors A B.

Definition real_rect_rat@{} q : real_rect I (rat q) = ind_rat I q
  := idpath.

Definition real_rect_lim@{} x : real_rect I (lim x) = ind_lim I x (approx_rect I x)
  := idpath.

Definition equiv_rect_rat_rat@{} q r e E : equiv_rect I (equiv_rat_rat q r e E)
  = ind_rat_rat I q r e E
  := idpath.

Definition equiv_rect_rat_lim@{} q y e d d' He xi
  : equiv_rect I (equiv_rat_lim q y e d d' He xi)
  = ind_rat_lim I q d d' e y (approx_rect I y) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_rat@{} x r e d d' He xi
  : equiv_rect I (equiv_lim_rat x r e d d' He xi)
  = ind_lim_rat I r d d' e x (approx_rect I x) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_lim@{} x y e d n e' He xi
  : equiv_rect I (equiv_lim_lim x y e d n e' He xi)
  = ind_lim_lim I x y (approx_rect I x) (approx_rect I y)
                  e d n e' He xi (equiv_rect I xi)
  := idpath.

End induction.

End VarSec.

End Cauchy.

Arguments equiv_path {Q _ _ _ _ _ _ _ _ _ _ _} x y _.


Section contents.
Context `{Funext} `{Universe.Univalence}.
Universe UQ.
Context (Q:Type@{UQ}) `{Rationals@{UQ UQ UQ UQ UQ UQ UQ UQ UQ UQ} Q}
  `{!TrivialApart Q} `{DecidablePaths Q}
  {Qmeet : Meet Q} {Qjoin : Join Q} `{!LatticeOrder Ale}
  `{!TotalRelation (@le Q _)} `{!Abs Q}.

Notation "Q+" := (Qpos.Qpos Q).


Notation rat := (rat Q).
Notation lim := (lim Q).

Definition real_rect0@{UA} (A : real Q -> Type@{UA})
  (val_rat : forall q, A (rat q))
  (val_lim : forall (x : Approximation Q) (a : forall e, A (x e)), A (lim x))
  (val_respects : forall u v (h : forall e, close e u v) (a : A u) (b : A v),
    equiv_path u v h # a = b)
  : forall x, A x.
Proof.
apply (real_rect Q A (fun _ _ _ _ _ _ => Unit)).
split;auto.
- intros. apply val_lim. intros;apply a.
- intros _ _ _ _ _ _. apply trunc_succ.
  (* ^ must be done by hand
       otherwise it uses some instance that needs a universe > Set *)
Defined.

Definition real_ind0@{UA} (A : real Q -> Type@{UA}) `{forall q, IsHProp (A q)}
  (A_rat : forall q, A (rat q))
  (A_lim : forall (x : Approximation Q) (a : forall e, A (x e)), A (lim x))
  : forall x, A x.
Proof.
apply real_rect0;auto.
intros. apply path_ishprop.
Defined.

Instance Requiv_refl@{} : forall e, Reflexive (close (A:=real Q) e).
Proof.
red. intros e u;revert u e.
apply (real_ind0 (fun u => forall e, _)).
- intros. apply equiv_rat_rat. hnf. rewrite plus_negate_r.
  split;[apply rings.flip_pos_negate|];apply Qpos.is_pos.
- intros. eapply equiv_lim_lim;[apply Qpos.pos_split3|].
  auto.
Qed.

Global Instance real_isset@{} : IsHSet (real Q).
Proof.
eapply @HSet.isset_hrel_subpaths.
3:apply equiv_path.
- red. intros;reflexivity.
- apply _.
Qed.

Definition const_approx@{} : real Q -> Approximation Q.
Proof.
intros x;exists (fun _ => x).
intros;reflexivity.
Defined.

Lemma lim_cons@{} : forall x, lim (const_approx x) = x.
Proof.
apply (real_ind0 _).
- intros. apply equiv_path.
  intros. eapply equiv_lim_rat;[apply Qpos.pos_split2|].
  simpl. reflexivity.
- intros x Hx. apply equiv_path. intros.
  eapply equiv_lim_lim;[|
  simpl; rewrite <-Hx;
  eapply equiv_lim_lim;[|simpl;reflexivity]].
  + path_via (e / 5 + e / 5 + (e * 3 / 5)).
    path_via (e * (5 / 5)).
    * rewrite pos_recip_r,pos_mult_1_r;reflexivity.
    * apply (pos_eq Q).
      change (' e * (5 / 5) = ' e / 5 + ' e / 5 + ' e * 3 / 5).
      ring_tac.ring_with_nat.
  + path_via (e / 5 + e / 5 + e / 5).
    apply (pos_eq Q).
    unfold cast,mult,Qpos_mult;simpl.
    unfold cast,dec_recip;simpl. ring_tac.ring_with_nat.
Qed.

Lemma lim_epi@{i j k} : epi.isepi@{UQ UQ i j k} lim.
Proof.
apply epi.issurj_isepi@{UQ UQ Uhuge Ularge i
  k Ularge j}.
apply BuildIsSurjection.
intros. apply tr. exists (const_approx b).
apply lim_cons.
Qed.

Definition equiv_rect0@{i} (P : forall e u v, close e u v -> Type@{i})
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
intros. apply @path_ishprop,trunc_succ.
Defined.

Definition equiv_rec0@{i} (P : Q+ -> real Q -> real Q -> Type@{i})
  `{forall e u v, IsHProp (P e u v)}
  := equiv_rect0 (fun e u v _ => P e u v).

Instance equiv_symm@{} : forall e, Symmetric (close (A:=real Q) e).
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

Lemma equiv_symm_rw@{i} : forall e u v,
  paths@{i} (close e u v) (close e v u).
Proof.
intros. apply path_universe_uncurried.
apply equiv_iff_hprop_uncurried.
split;apply equiv_symm.
Qed.

Section mutual_recursion.

Record Recursors@{UA UB} (A : Type@{UA}) (B : Q+ -> A -> A -> Type@{UB}) :=
  { rec_rat : Q -> A
  ; rec_lim : Approximation Q ->
      forall val_ind : Q+ -> A,
      (forall d e, B (d + e) (val_ind d) (val_ind e)) -> A
  ; rec_separated : forall x y, (forall e, B e x y) -> x = y
  ; rec_hprop : forall e x y, IsHProp (B e x y)
  ; rec_rat_rat : forall q r e, - ' e < q - r < ' e -> B e (rec_rat q) (rec_rat r)
  ; rec_rat_lim : forall q d d' e (y : Approximation Q) (b : Q+ -> A)
      (Eb : forall d e, B (d + e) (b d) (b e)),
      e = d + d' -> close d' (rat q) (y d) ->
      B d' (rec_rat q) (b d) ->
      B e (rec_rat q) (rec_lim y b Eb)
  ; rec_lim_rat : forall r d d' e (x : Approximation Q) (a : Q+ -> A)
      (Ea : forall d e, B (d+e) (a d) (a e)),
      e = d + d' ->
      close d' (x d) (rat r) ->
      B d' (a d) (rec_rat r) ->
      B e (rec_lim x a Ea) (rec_rat r)
  ; rec_lim_lim : forall (x y : Approximation Q) (a b : Q+ -> A)
      (Ea : forall d e, B (d + e) (a d) (a e))
      (Eb : forall d e, B (d + e) (b d) (b e))
      e d n e',
      e = d + n + e' ->
      close e' (x d) (y n) ->
      B e' (a d) (b n) ->
      B e (rec_lim x a Ea) (rec_lim y b Eb) }.

Definition recursors_inductors@{UA UB}
  : forall (A : Type@{UA}) (B : Q+ -> A -> A -> Type@{UB}), Recursors A B ->
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
  : forall x y e, close e x y -> B e (real_rec A B I x) (real_rec A B I y)
  := (equiv_rect Q) _ _ (recursors_inductors A B I).

Definition real_rec_rat A B I q : real_rec A B I (rat q) = rec_rat _ _ I q
  := idpath.

Definition real_rec_lim A B I x : real_rec A B I (lim x) =
  rec_lim _ _ I x (fun e => real_rec A B I (x e))
    (fun d e => equiv_rec A B I _ _ _ (approx_equiv Q x d e))
  := idpath.

End mutual_recursion.

Instance Q_close_symm@{} : forall e, Symmetric (@close _ Q _ e).
Proof.
red;unfold close;simpl.
intros e x y [E1 E2];split.
- apply flip_lt_negate. rewrite <-negate_swap_r,involutive.
  trivial.
- apply flip_lt_negate.
  rewrite negate_swap_r,involutive. trivial.
Qed.

Lemma separate_mult@{} : forall l u v, (forall e, close (l * e) u v) -> u = v.
Proof.
intros l x y E. apply equiv_path.
intros. assert (Hrw : e = l * (e / l)).
+ path_via ((l / l) * e).
   * rewrite pos_recip_r. apply symmetry,Qpos_mult_1_l.
   * apply (pos_eq Q). ring_tac.ring_with_nat.
+ rewrite Hrw;apply E.
Qed.

Lemma Q_triangular_one@{} : forall (q r : Q)
(e : Q+) (Hqr : close e q r)
(q0 : Q) (n : Q+),
  (close n q q0 → close (e + n) r q0).
Proof.
unfold close;simpl.
intros q r e [E1 E1'] s n [E2 E2'].
split.
- apply flip_lt_negate. rewrite negate_swap_r,!involutive.
  apply flip_lt_negate in E2.
  rewrite negate_swap_r,!involutive in E2.
  pose proof (plus_lt_compat _ _ _ _ E1' E2) as E.
  assert (Hrw : s - r = q - r + (s - q));[|rewrite Hrw;trivial].
  path_via (s - r + 0).
  { rewrite plus_0_r;trivial. }
  rewrite <-(plus_negate_r q). ring_tac.ring_with_nat.
- apply flip_lt_negate in E1.
  rewrite negate_swap_r,!involutive in E1.
  pose proof (plus_lt_compat _ _ _ _ E1 E2') as E.
  assert (Hrw : r - s = r - q + (q - s));[|rewrite Hrw;trivial].
  path_via (r - s + 0).
  { rewrite plus_0_r;trivial. }
  rewrite <-(plus_negate_r q). ring_tac.ring_with_nat.
Qed.

Instance Q_triangular@{} : Triangular Q+ Q.
Proof.
hnf. intros u v w e d E1 E2.
apply Q_triangular_one with v.
- Symmetry;trivial.
- trivial.
Qed.

Section Requiv_alt.

Definition rounded_halfrel@{} := sigT@{Ularge UQ}
  (fun half : real Q -> Q+ -> TruncType@{UQ} -1 =>
  (forall u e, half u e <-> merely (exists d d', e = d + d' /\ half u d))
  /\ (forall u v n e, close e u v ->
    ((half u n -> half v (n+e)) /\ (half v n -> half u (n+e))))).

Definition rounded_halfrel_close@{} e (R1 R2 : rounded_halfrel)
  := forall u n, (R1.1 u n -> R2.1 u (e+n)) /\ (R2.1 u n -> R1.1 u (e+n)).

Definition rounded_zeroary@{} := sigT@{Ularge UQ}
  (fun R : Q+ -> TruncType@{UQ} -1 =>
    forall e, R e <-> merely (exists d d', e = d + d' /\ R d)).

Definition rounded_zeroary_close@{} e (R1 R2 : rounded_zeroary)
  := forall n, (R1.1 n -> R2.1 (e+n)) /\ (R2.1 n -> R1.1 (e+n)).

Lemma rounded_halfrel_separated' : forall u v,
  (forall e, rounded_halfrel_close e u v) -> u = v.
Proof.
intros u v E. eapply Sigma.path_sigma@{Ularge UQ Ularge}. Unshelve.
apply path_ishprop.
apply path_forall. intro x. apply path_forall. intro e.
apply TruncType.path_iff_hprop_uncurried.
unfold rounded_halfrel_close in E.
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

Definition rounded_halfrel_separated@{}
  := rounded_halfrel_separated'@{Ularge Ularge Ularge Uhuge}.

Instance rounded_halfrel_close_hprop@{}
  : forall e u v, IsHProp (rounded_halfrel_close e u v).
Proof.
unfold rounded_halfrel_close. intros. apply _.
Qed.

Instance Qclose_separating : Separated Q+ Q.
Proof. Admitted.

Lemma Qclose_rounded@{} : ∀ (q r : Q) e, close e q r ↔
  merely (∃ d d' : Q+, e = d + d' ∧ close d q r).
Proof. Admitted.

Definition Requiv_alt_rat_rat@{} (q r : Q) : rounded_zeroary.
Proof.
exists (fun e => BuildhProp (close e q r)).
simpl. apply Qclose_rounded.
Defined.

Lemma rat_lim_rounded_step@{} :
  ∀ val_ind : Q+ → rounded_zeroary,
  (∀ d e : Q+, rounded_zeroary_close (d + e) (val_ind d) (val_ind e)) ->
  ∀ e : Q+,
  merely (∃ d d' : Q+, e = d + d' ∧ (val_ind d).1 d')
  ↔ merely (∃ d d' : Q+,
     e = d + d' ∧ merely (∃ d0 d'0 : Q+, d = d0 + d'0 ∧ (val_ind d0).1 d'0)).
Proof.
unfold rounded_zeroary_close. intros a Ea e.
split;apply (Trunc_ind _);intros [d [d' [He E]]].
- generalize (fst ((a _).2 _) E);apply (Trunc_ind _).
  intros [n [n' [Hd' E1]]].
  apply tr;do 2 econstructor;split;
  [|apply tr;do 2 econstructor;split;[reflexivity|exact E1]].
  path_via (d+n+n').
  rewrite He,Hd'. apply (pos_eq Q),plus_assoc.
- revert E;apply (Trunc_ind _);intros [n [n' [Hd E]]].
  apply tr;do 2 econstructor;split;[|eapply Ea,E].
  path_via (d'/2 + (n + d'/2 + n')).
  rewrite <-(pos_unconjugate Q 2 d') in He. rewrite He,Hd.
  apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_alt_rat_lim@{}
  : ∀ val_ind : Q+ → rounded_zeroary,
  (∀ d e : Q+, rounded_zeroary_close (d + e) (val_ind d) (val_ind e)) →
  rounded_zeroary.
Proof.
intros val_ind IH.
exists (fun e => merely (exists d d', e = d + d' /\ (val_ind d).1 d')).
apply rat_lim_rounded_step. trivial.
Defined.

Lemma rounded_zeroary_separated' : ∀ x y : rounded_zeroary,
  (∀ e : Q+, rounded_zeroary_close e x y) → x = y.
Proof.
intros x y E.
unfold rounded_zeroary,rounded_zeroary_close in *;
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

Definition rounded_zeroary_separated@{}
  := rounded_zeroary_separated'@{Ularge Ularge Uhuge}.

Lemma Requiv_alt_rat_rat_rat_pr@{} :
∀ (q q0 r : Q) (e : Q+),
- ' e < q0 - r < ' e
→ rounded_zeroary_close e ((λ r0 : Q, Requiv_alt_rat_rat q r0) q0)
    ((λ r0 : Q, Requiv_alt_rat_rat q r0) r).
Proof.
unfold Requiv_alt_rat_rat.
red;simpl. intros q r1 r2 e Hr n.
split.
- intros E;apply symmetry.
  apply symmetry in E;revert E;apply Q_triangular_one. trivial.
- intros E;apply symmetry.
  apply symmetry in E;revert E;apply Q_triangular. trivial.
Qed.

Lemma Requiv_alt_rat_rat_lim_pr@{} :
∀ (q q0 : Q) (d d' e : Q+) (y : Approximation Q) (b : Q+ → rounded_zeroary)
(Eb : ∀ d0 e0 : Q+, rounded_zeroary_close (d0 + e0) (b d0) (b e0)),
e = d + d'
→ close d' (rat q0) (y d)
  → rounded_zeroary_close d' ((λ r : Q, Requiv_alt_rat_rat q r) q0) (b d)
    → rounded_zeroary_close e ((λ r : Q, Requiv_alt_rat_rat q r) q0)
        ((λ _ : Approximation Q, Requiv_alt_rat_lim) y b Eb).
Proof.
unfold rounded_zeroary_close;simpl. intros q q' d d' e y b Eb He xi IH e'.
split.
- intros E1.
  pose proof (fst (IH _) E1) as E2.
  apply tr. exists d, (d' + e').
  split;trivial.
  rewrite He. apply (pos_eq Q);ring_tac.ring_with_nat.
- apply (Trunc_ind _). intros [n [n' [He' E1]]].
  pose proof (fst (Eb _ d _) E1) as E2.
  apply IH in E2.
  rewrite He,He'.
  assert (Hrw : (d + d' + (n + n')) = (d' + (n + d + n')))
  by (apply (pos_eq Q);ring_tac.ring_with_nat).
  rewrite Hrw;trivial.
Qed.

Lemma Requiv_alt_rat_lim_rat_pr@{} :
∀ (q r : Q) (d d' e : Q+) (x : Approximation Q) (a : Q+ → rounded_zeroary)
(Ea : ∀ d0 e0 : Q+, rounded_zeroary_close (d0 + e0) (a d0) (a e0)),
e = d + d'
→ close d' (x d) (rat r)
  → rounded_zeroary_close d' (a d) ((λ r0 : Q, Requiv_alt_rat_rat q r0) r)
    → rounded_zeroary_close e ((λ _ : Approximation Q, Requiv_alt_rat_lim) x a Ea)
        ((λ r0 : Q, Requiv_alt_rat_rat q r0) r).
Proof.
unfold rounded_zeroary_close;simpl;intros q r d d' e x a Ea He xi IH e'.
split.
- apply (Trunc_ind _). intros [n [n' [He' E1]]].
  pose proof (fst (Ea _ d _) E1) as E2.
  apply IH in E2.
  rewrite He,He'.
  assert (Hrw : (d + d' + (n + n')) = (d' + (n + d + n')))
  by (apply (pos_eq Q);ring_tac.ring_with_nat).
  rewrite Hrw;trivial.
- intros E1.
  pose proof (snd (IH _) E1) as E2.
  apply tr. exists d, (d' + e').
  split;trivial.
  rewrite He. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_rat_lim_lim_pr@{} :
∀ (x y : Approximation Q) (a b : Q+ → rounded_zeroary)
(Ea : ∀ d e : Q+, rounded_zeroary_close (d + e) (a d) (a e))
(Eb : ∀ d e : Q+, rounded_zeroary_close (d + e) (b d) (b e)) (e d n n' : Q+),
e = d + n + n'
→ close n' (x d) (y n)
  → rounded_zeroary_close n' (a d) (b n)
    → rounded_zeroary_close e ((λ _ : Approximation Q, Requiv_alt_rat_lim) x a Ea)
        ((λ _ : Approximation Q, Requiv_alt_rat_lim) y b Eb).
Proof.
unfold rounded_zeroary_close;simpl;intros x y a b Ea Eb e d n n' He xi IH.
intros e';split;apply (Trunc_ind _).
- intros [d0 [d0' [He' E1]]].
  apply tr.
  pose proof (fst (Ea _ d _) E1) as E2.
  apply (fst (IH _)) in E2.
  exists n, (n' + (d0 + d + d0')).
  split;trivial.
  rewrite He,He'. apply (pos_eq Q); ring_tac.ring_with_nat.
- intros [d0 [d0' [He' E1]]].
  apply tr.
  pose proof (fst (Eb _ n _) E1) as E2.
  apply (snd (IH _)) in E2.
  exists d, (n' + (d0 + n + d0')).
  split;trivial.
  rewrite He,He'. apply (pos_eq Q); ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_rat_ok@{} : forall (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(r : Q) (e : Q+),
merely (∃ d d' : Q+, e = d + d' ∧ (Requiv_alt_x_e d).1 (rat r) d')
↔ merely
    (∃ d d' : Q+,
     e = d + d'
     ∧ merely
         (∃ d0 d'0 : Q+, d = d0 + d'0 ∧ (Requiv_alt_x_e d0).1 (rat r) d'0)).
Proof.
intros a Ea r e.
split;apply (Trunc_ind _);intros [d [d' [He E]]].
- generalize (fst (fst (a _).2 _ _) E);apply (Trunc_ind _).
  intros [n [n' [Hd' E1]]].
  apply tr;do 2 econstructor;split;
  [|apply tr;do 2 econstructor;split;[reflexivity|exact E1]].
  path_via (d+n+n').
  rewrite He,Hd'. apply (pos_eq Q),plus_assoc.
- revert E;apply (Trunc_ind _);intros [n [n' [Hd E]]].
  apply tr;do 2 econstructor;split;[|eapply Ea,E].
  path_via (d'/2 + (n + d'/2 + n')).
  rewrite <-(pos_unconjugate Q 2 d') in He. rewrite He,Hd.
  apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_alt_lim_rat@{} : forall (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(r : Q), rounded_zeroary.
Proof.
intros ???.
red. exists (fun e => merely (exists d d' : Q+, e = d + d' /\
  (Requiv_alt_x_e d).1 (rat r) d')).
apply Requiv_alt_lim_rat_ok;trivial.
Defined.

Lemma Requiv_alt_lim_lim_ok@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(y : Approximation Q)
(e : Q+)
  : merely (∃ d d' n : Q+, e = d + d' + n ∧ (Requiv_alt_x_e d).1 (y n) d')
    ↔ merely
    (∃ d d' : Q+,
     e = d + d'
     ∧ merely
         (∃ d0 d'0 n : Q+, d = d0 + d'0 + n ∧ (Requiv_alt_x_e d0).1 (y n) d'0)).
Proof.
pose proof (fun e => (Requiv_alt_x_e e).2) as E1.
red in IHx. simpl in E1.
split;apply (Trunc_ind _).
- intros [d [d' [n [He E2]]]].
  apply (merely_destruct (fst (fst (E1 _) _ _) E2)).
  intros [d0 [d0' [Hd' E3]]].
  apply tr;exists (d+d0+n);exists d0';split;
  [|apply tr;econstructor;econstructor;econstructor;split;[reflexivity|exact E3]].
  rewrite He,Hd'. apply (pos_eq Q); ring_tac.ring_with_nat.
- intros [d [d' [He E2]]]. revert E2;apply (Trunc_ind _).
  intros [d0 [d0' [n [Hd E2]]]].
  pose proof (fun e u v n e0 xi => fst (snd (E1 e) u v n e0 xi)) as E3.
  pose proof (fun a b c c' => E3 c _ _ c' _ (approx_equiv Q y a b)) as E4;clear E3.
  pose proof (fun a => E4 _ a _ _ E2) as E3. clear E4.
  rewrite Hd in He.
  apply tr;repeat econstructor;[|exact (E3 (d' / 2))].
  path_via (d0 + d0' + n + (2 / 2) * d').
  + rewrite pos_recip_r,Qpos_mult_1_l.
    trivial.
  + apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_alt_lim_lim@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(y : Approximation Q) : rounded_zeroary.
Proof.
red.
exists (fun e => merely (exists d d' n, e = d + d' + n /\
  (Requiv_alt_x_e d).1 (y n) d')).
apply Requiv_alt_lim_lim_ok. trivial.
Defined.

Lemma Requiv_alt_lim_lim_rat_lim_rat_pr@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(q r : Q) (e : Q+)
(He : - ' e < q - r < ' e)
  : rounded_zeroary_close e (Requiv_alt_lim_rat Requiv_alt_x_e IHx q)
    (Requiv_alt_lim_rat Requiv_alt_x_e IHx r).
Proof.
red. unfold Requiv_alt_lim_rat;simpl. red in IHx.
pose proof (fun e => (Requiv_alt_x_e e).2) as Requiv_alt_x_e_pr.
simpl in Requiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d [d' [Hn E1]]].
  pose proof (equiv_rat_rat Q _ _ _ He) as E2.
  pose proof (fst (snd (Requiv_alt_x_e_pr _) _ _ _ _ E2) E1) as E3.
  change (Cauchy.rat Q) with rat in E3.
  apply tr;exists d, (d'+e);split;[|exact E3].
  rewrite Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
- intros [d [d' [Hn E1]]].
  pose proof (equiv_rat_rat Q _ _ _ He) as E2.
  pose proof (snd (snd (Requiv_alt_x_e_pr _) _ _ _ _ E2) E1) as E3.
  change (Cauchy.rat Q) with rat in E3.
  apply tr;exists d, (d'+e);split;[|exact E3].
  rewrite Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_lim_rat_lim_lim_pr@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(q : Q) (d d' e : Q+) (y : Approximation Q) (b : Q+ → rounded_zeroary)
(IHb : ∀ d0 e0 : Q+, rounded_zeroary_close (d0 + e0) (b d0) (b e0))
(He : e = d + d')
(xi : close d' (rat q) (y d))
  : rounded_zeroary_close d' (Requiv_alt_lim_rat Requiv_alt_x_e IHx q) (b d) ->
    rounded_zeroary_close e (Requiv_alt_lim_rat Requiv_alt_x_e IHx q)
              (Requiv_alt_lim_lim Requiv_alt_x_e IHx y).
Proof.
unfold rounded_zeroary_close,Requiv_alt_lim_rat,Requiv_alt_lim_lim;simpl;intros E1.
pose proof (fun e => (Requiv_alt_x_e e).2) as Requiv_alt_x_e_pr.
simpl in Requiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d0 [d0' [Hn E2]]].
  pose proof (fst (snd (Requiv_alt_x_e_pr _) _ _ _ _ xi) E2) as E3.
  apply tr;do 3 econstructor;split;[|exact E3].
  rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
- intros [d0 [d0' [n0 [Hn E2]]]].
  pose proof (fun a b => snd (snd (Requiv_alt_x_e_pr a) _ _ b _ xi) ) as E3.
  pose proof (fun a b a' b' => snd (snd (Requiv_alt_x_e_pr a) _ _ b _
    (approx_equiv Q y a' b'))) as E4.
  pose proof (fun a => E4 _ _ a _ E2) as E5. clear E4.
  pose proof (E3 _ _ (E5 _)) as E4. clear E3 E5.
  apply tr;do 2 econstructor;split;[|exact E4].
  rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_lim_lim_lim_rat_pr@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(r : Q) (d d' e : Q+) (x : Approximation Q) (a : Q+ → rounded_zeroary)
(IHa : ∀ d0 e0 : Q+, rounded_zeroary_close (d0 + e0) (a d0) (a e0))
(He : e = d + d')
(xi : close d' (x d) (rat r))
  : rounded_zeroary_close d' (a d) (Requiv_alt_lim_rat Requiv_alt_x_e IHx r) ->
    rounded_zeroary_close e (Requiv_alt_lim_lim Requiv_alt_x_e IHx x)
              (Requiv_alt_lim_rat Requiv_alt_x_e IHx r).
Proof.
unfold rounded_zeroary_close,Requiv_alt_lim_rat,Requiv_alt_lim_lim;simpl;intros E1.
pose proof (fun e => (Requiv_alt_x_e e).2) as Requiv_alt_x_e_pr.
simpl in Requiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d0 [d0' [n0 [Hn E2]]]].
  pose proof (fun a b => fst (snd (Requiv_alt_x_e_pr a) _ _ b _ xi) ) as E3.
  pose proof (fun a b a' b' => fst (snd (Requiv_alt_x_e_pr a) _ _ b _
    (approx_equiv Q x a' b'))) as E4.
  pose proof (fun a => E4 _ _ _ a E2) as E5. clear E4.
  pose proof (E3 _ _ (E5 _)) as E4. clear E3 E5.
  apply tr;do 2 econstructor;split;[|exact E4].
  rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
- intros [d0 [d0' [Hn E2]]].
  pose proof (snd (snd (Requiv_alt_x_e_pr _) _ _ _ _ xi) E2) as E3.
  apply tr;do 3 econstructor;split;[|exact E3].
  rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_lim_lim_lim_lim_pr@{} (Requiv_alt_x_e : Q+ → rounded_halfrel)
(IHx : ∀ d e : Q+, rounded_halfrel_close (d + e)
  (Requiv_alt_x_e d) (Requiv_alt_x_e e))
(x y : Approximation Q) (a b : Q+ → rounded_zeroary)
(IHa : ∀ d e : Q+, rounded_zeroary_close (d + e) (a d) (a e))
(IHb : ∀ d e : Q+, rounded_zeroary_close (d + e) (b d) (b e))
(e d n e' : Q+)
(He : e = d + n + e')
(xi : close e' (x d) (y n))
(IH : rounded_zeroary_close e' (a d) (b n))
  : rounded_zeroary_close e (Requiv_alt_lim_lim Requiv_alt_x_e IHx x)
              (Requiv_alt_lim_lim Requiv_alt_x_e IHx y).
Proof.
red in IH. red. unfold Requiv_alt_lim_lim;simpl.
clear IH IHa IHb a b.
pose proof (fun e => (Requiv_alt_x_e e).2) as Requiv_alt_x_e_pr.
simpl in Requiv_alt_x_e_pr.
intros n0;split;apply (Trunc_ind _);intros [d0 [d' [n1 [Hn0 E1]]]].
- pose proof (fun f g => fst (snd (Requiv_alt_x_e_pr f) _ _ g _ xi)) as E2.
  pose proof (fun f g h i => fst (snd (Requiv_alt_x_e_pr f) _ _ g _
    (approx_equiv Q x h i))) as E3.
  pose proof (E2 _ _ (E3 _ _ _ _ E1)) as E4.
  apply tr;do 3 econstructor;split;[|exact E4].
  rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
- pose proof (fun f g => snd (snd (Requiv_alt_x_e_pr f) _ _ g _ xi)) as E2.
  pose proof (fun f g h i => snd (snd (Requiv_alt_x_e_pr f) _ _ g _
    (approx_equiv Q y h i))) as E3.
  pose proof (E2 _ _ (E3 _ _ _ _ E1)) as E4.
  apply tr;do 3 econstructor;split;[|exact E4].
  rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma rounded_zeroary_to_rounded_halfrel_second@{}
  (I : Recursors@{Ularge UQ} rounded_zeroary rounded_zeroary_close)
  (R := real_rec rounded_zeroary rounded_zeroary_close I
    : real Q → rounded_zeroary)
  : forall (u v : real Q) (n e : Q+),
    close e u v
    → ((R u).1 n → (R v).1 (n + e)) ∧ ((R v).1 n → (R u).1 (n + e)).
Proof.
pose proof (equiv_rec rounded_zeroary rounded_zeroary_close I) as R_pr.
red in R_pr.
change (real_rec rounded_zeroary rounded_zeroary_close I) with R in R_pr.
intros u v n e xi.
rewrite !(qpos_plus_comm Q n).
apply (R_pr u v e xi n).
Qed.

Definition rounded_zeroary_to_rounded_halfrel@{}
  : Recursors@{Ularge UQ} rounded_zeroary rounded_zeroary_close -> rounded_halfrel.
Proof.
intros I.
pose (R := real_rec rounded_zeroary rounded_zeroary_close I).
exists (fun r => (R r).1).
split.
- exact (fun u => (R u).2).
- apply rounded_zeroary_to_rounded_halfrel_second.
Defined.

Instance rounded_zeroary_close_hprop@{} : forall e a b,
  IsHProp (rounded_zeroary_close e a b).
Proof.
unfold rounded_zeroary_close;apply _.
Qed.

Definition Requiv_alt_rat@{} : Q -> rounded_halfrel.
Proof.
intros q. apply rounded_zeroary_to_rounded_halfrel.
simple refine (Build_Recursors rounded_zeroary rounded_zeroary_close
  _ _ rounded_zeroary_separated rounded_zeroary_close_hprop _ _ _ _).
- intros r. apply (Requiv_alt_rat_rat q r).
- intros _. apply Requiv_alt_rat_lim.
- exact (Requiv_alt_rat_rat_rat_pr q).
- exact (Requiv_alt_rat_rat_lim_pr q).
- exact (Requiv_alt_rat_lim_rat_pr q).
- exact Requiv_alt_rat_lim_lim_pr.
Defined.

Definition Requiv_alt_rat_lim_compute@{} : forall q x e,
  paths@{Ularge} ((Requiv_alt_rat q).1 (lim x) e)
  (merely (exists d d', e = d + d' /\ (Requiv_alt_rat q).1 (x d) d')).
Proof.
reflexivity.
Defined.

Definition Requiv_alt_lim@{} : forall (Requiv_alt_x_e : Q+ -> rounded_halfrel),
  (∀ d e : Q+, rounded_halfrel_close (d + e)
    (Requiv_alt_x_e d) (Requiv_alt_x_e e)) -> rounded_halfrel.
Proof.
intros Requiv_alt_x_e IHx.
(* forall e u n, Requiv_alt_x_e e u n means Requiv_alt n (x e) u *)
apply rounded_zeroary_to_rounded_halfrel.
simple refine (Build_Recursors rounded_zeroary rounded_zeroary_close
  _ _ rounded_zeroary_separated rounded_zeroary_close_hprop _ _ _ _).
- exact (Requiv_alt_lim_rat _ IHx).
- intros y _ _;exact (Requiv_alt_lim_lim Requiv_alt_x_e IHx y).
- apply Requiv_alt_lim_lim_rat_lim_rat_pr.
- simpl. apply Requiv_alt_lim_lim_rat_lim_lim_pr.
- simpl. apply Requiv_alt_lim_lim_lim_lim_rat_pr.
- simpl. apply Requiv_alt_lim_lim_lim_lim_lim_pr.
Defined.

Lemma Requiv_alt_lim_lim_compute@{} : forall (a : Q+ -> rounded_halfrel) Ea x e,
  paths@{Ularge} ((Requiv_alt_lim a Ea).1 (lim x) e)
  (merely (exists d d' n, e = d + d' + n /\
    (a d).1 (x n) d')).
Proof.
reflexivity.
Defined.

Lemma Requiv_alt_rat_rat_pr@{} : ∀ (q r : Q) (e : Q+), - ' e < q - r < ' e →
  rounded_halfrel_close e (Requiv_alt_rat q) (Requiv_alt_rat r).
Proof.
intros q r e Hqr.
red. apply (real_ind0 (fun u => forall n, _)).
- simpl. split; apply Q_triangular_one; trivial. Symmetry;trivial.
- intros x Ex n.
  rewrite !Requiv_alt_rat_lim_compute.
  split;apply (Trunc_ind _);intros [d [d' [Hn E1]]].
  + apply Ex in E1. apply tr;do 2 econstructor;split;[|exact E1].
    rewrite Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
  + apply Ex in E1. apply tr;do 2 econstructor;split;[|exact E1].
    rewrite Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_rat_lim_pr@{} : ∀ (q : Q) (d d' e : Q+) (y : Approximation Q)
(b : Q+ → rounded_halfrel)
(Eb : ∀ d0 e0 : Q+, rounded_halfrel_close (d0 + e0) (b d0) (b e0)),
e = d + d'
→ close d' (rat q) (y d)
  → rounded_halfrel_close d' (Requiv_alt_rat q) (b d)
    → rounded_halfrel_close e (Requiv_alt_rat q) (Requiv_alt_lim b Eb).
Proof.
intros q d d' e y b Eb He xi IH.
red. apply (real_ind0 (fun u => forall n, _)).
- simpl. intros q0 n.
  red in IH. pose proof (fun x => IH (rat x)) as E1.
  simpl in E1. clear IH. split.
  + intros E2.
    apply E1 in E2. apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He;apply (pos_eq Q);ring_tac.ring_with_nat.
  + apply (Trunc_ind _);intros [d0 [d0' [Hn E2]]].
    rewrite He.
    assert (Hrw : (d + d' + n) = d' + (d + n))
    by (apply (pos_eq Q);ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    apply E1.
    rewrite Hn.
    red in Eb.
    pose proof (fst (Eb _ d _ _) E2) as E3.
    assert (Hrw : (d + (d0 + d0')) = (d0 + d + d0'))
    by (apply (pos_eq Q);ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    trivial.
- intros x Ex n.
  rewrite !Requiv_alt_rat_lim_compute,!Requiv_alt_lim_lim_compute.
  split;apply (Trunc_ind _).
  + intros [d0 [d0' [Hn E1]]].
    apply IH in E1.
    apply tr;do 3 econstructor;split;[|exact E1].
    rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
  + intros [d0 [d0' [n0 [Hn E1]]]].
    red in Eb. pose proof (fst (Eb _ d _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_rat_pr@{} : ∀ (r : Q) (d d' e : Q+) (x : Approximation Q)
(a : Q+ → rounded_halfrel)
(Ea : ∀ d0 e0 : Q+, rounded_halfrel_close (d0 + e0) (a d0) (a e0)),
e = d + d'
→ close d' (x d) (rat r)
  → rounded_halfrel_close d' (a d) (Requiv_alt_rat r)
    → rounded_halfrel_close e (Requiv_alt_lim a Ea) (Requiv_alt_rat r).
Proof.
intros r d d' e x a Ea He xi IH.
red. apply (real_ind0 (fun u => forall n, _)).
- simpl. intros q n;split.
  + apply (Trunc_ind _). intros [d0 [d0' [Hn E1]]].
    pose proof (fun x => fst (Ea _ x _ _) E1) as E2.
    pose proof (fst (IH _ _) (E2 _)) as E3.
    simpl in E3.
    rewrite He,Hn.
    assert (Hrw : (d + d' + (d0 + d0')) = (d' + (d0 + d + d0')))
    by (apply (pos_eq Q);ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    trivial.
  + intros E1.
    red in IH.
    pose proof (snd (IH (rat _) _) E1) as E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He. apply (pos_eq Q);ring_tac.ring_with_nat.
- intros y Ey n.
  rewrite !Requiv_alt_rat_lim_compute,!Requiv_alt_lim_lim_compute.
  split;apply (Trunc_ind _).
  + intros [d0 [d0' [n0 [Hn E1]]]].
    pose proof (fun x => fst (Ea _ x _ _) E1) as E2.
    pose proof (fst (IH _ _) (E2 _)) as E3.
    apply tr;do 2 econstructor;split;[|exact E3].
    rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
  + intros [d0 [d0' [Hn E1]]].
    pose proof (snd (IH _ _) E1) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma Requiv_alt_lim_lim_pr@{} : ∀ (x y : Approximation Q)
  (a b : Q+ → rounded_halfrel)
  (Ea : ∀ d e : Q+, rounded_halfrel_close (d + e) (a d) (a e))
  (Eb : ∀ d e : Q+, rounded_halfrel_close (d + e) (b d) (b e)) (e d n e' : Q+),
  e = d + n + e'
  → close e' (x d) (y n)
  → rounded_halfrel_close e' (a d) (b n)
  → rounded_halfrel_close e (Requiv_alt_lim a Ea) (Requiv_alt_lim b Eb).
Proof.
intros x y a b Ea Eb e d n e' He xi IH.
red. apply (real_ind0 (fun u => forall n0, _)).
- intros q n0.
  simpl. split;apply (Trunc_ind _).
  + intros [d0 [d' [Hn0 E1]]].
    pose proof (fst (Ea _ d _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
  + intros [d0 [d' [Hn0 E1]]].
    pose proof (fst (Eb _ n _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
- intros z Ez n0.
  simpl.
  split;apply (Trunc_ind _).
  + intros [d0 [d' [n1 [Hn0 E1]]]].
    pose proof (fst (IH _ _) (fst (Ea _ _ _ _) E1)) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
  + intros [d0 [d' [n1 [Hn0 E1]]]].
    pose proof (snd (IH _ _) (fst (Eb _ _ _ _) E1)) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_alt_rounded_halfrel@{} : real Q -> rounded_halfrel.
Proof.
apply (real_rec rounded_halfrel rounded_halfrel_close).
apply (Build_Recursors rounded_halfrel rounded_halfrel_close
  Requiv_alt_rat (fun _ => Requiv_alt_lim)
  rounded_halfrel_separated rounded_halfrel_close_hprop).
- exact Requiv_alt_rat_rat_pr.
- exact Requiv_alt_rat_lim_pr.
- exact Requiv_alt_lim_rat_pr.
- exact Requiv_alt_lim_lim_pr.
Defined.

Definition Requiv_alt : Q+ -> real Q -> real Q -> Type
  := fun e x y => (Requiv_alt_rounded_halfrel x).1 y e.

Definition Requiv_alt_rat_rat_def@{} : forall e q r,
  paths@{Ularge} (Requiv_alt e (rat q) (rat r)) (close e q r).
Proof.
intros;exact idpath.
Defined.

Definition Requiv_alt_rat_lim_def@{} : forall e q y,
  paths@{Ularge} (Requiv_alt e (rat q) (lim y))
  (merely (exists d d', e = d + d' /\ Requiv_alt d' (rat q) (y d))).
Proof.
intros;exact idpath.
Defined.

Definition Requiv_alt_lim_rat_def@{} : forall e x r,
  paths@{Ularge} (Requiv_alt e (lim x) (rat r))
  (merely (exists d d', e = d + d' /\ Requiv_alt d' (x d) (rat r))).
Proof.
intros;exact idpath.
Defined.

Definition Requiv_alt_lim_lim_def@{} : forall e x y,
  paths@{Ularge} (Requiv_alt e (lim x) (lim y))
  (merely (exists d d' n, e = d + d' + n /\ Requiv_alt d' (x d) (y n))).
Proof.
intros;exact idpath.
Defined.

Lemma Requiv_alt_round@{} : forall e u v, Requiv_alt e u v <->
  merely (exists d d', e = d + d' /\ Requiv_alt d u v).
Proof.
intros. apply ((Requiv_alt_rounded_halfrel u).2).
Qed.

Lemma Requiv_alt_Requiv@{} : forall u v w n e, Requiv_alt n u v -> close e v w ->
  Requiv_alt (n+e) u w.
Proof.
intros ????? E1 E2.
apply (snd (Requiv_alt_rounded_halfrel u).2 _ _ _ _ E2). trivial.
Qed.

Lemma Requiv_Requiv_alt : forall u v w n e, close n u v -> Requiv_alt e v w ->
  Requiv_alt (n+e) u w.
Proof.
intros ????? E1 E2.
pose proof (fun x y => snd (Requiv_alt_rounded_halfrel x).2 _ _ y _ E1).
(* do we need to prove Symmetric (Requiv_alt _)? *)
(* We don't actually need this lemma
   as we just rewrite Requiv_alt = Requiv in the previous one. *)
Abort.

Lemma Requiv_to_Requiv_alt' : forall e u v, close e u v -> Requiv_alt e u v.
Proof.
apply (equiv_rec0 _).
- auto.
- intros q y e d d' He _ IH.
  rewrite Requiv_alt_rat_lim_def. apply tr;eauto.
- intros;rewrite Requiv_alt_lim_rat_def;apply tr;eauto.
- intros x y e d n e' He _ IH;rewrite Requiv_alt_lim_lim_def.
  apply tr;do 3 econstructor;split;[|exact IH].
  rewrite He;apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_to_Requiv_alt@{}
  := Requiv_to_Requiv_alt'@{UQ UQ UQ}.

Lemma Requiv_alt_to_Requiv' : forall e u v, Requiv_alt e u v -> close e u v.
Proof.
intros e u v;revert u v e.
apply (real_ind0 (fun u => forall v e, _ -> _)).
- intros q;apply (real_ind0 (fun v => forall e, _ -> _)).
  + intros r e;rewrite Requiv_alt_rat_rat_def.
    apply equiv_rat_rat.
  + intros x Ex e;rewrite Requiv_alt_rat_lim_def.
    apply (Trunc_ind _);intros [d [d' [He E1]]].
    eapply equiv_rat_lim;eauto.
- intros x Ex;apply (real_ind0 (fun v => forall e, _ -> _)).
  + intros r e;rewrite Requiv_alt_lim_rat_def.
    apply (Trunc_ind _);intros [d [d' [He E1]]].
    eapply equiv_lim_rat;eauto.
  + intros y Ey e;rewrite Requiv_alt_lim_lim_def.
    apply (Trunc_ind _);intros [d [d' [n [He E1]]]].
    eapply equiv_lim_lim;[|eauto].
    rewrite He;apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition Requiv_alt_to_Requiv@{}
  := Requiv_alt_to_Requiv'@{UQ UQ UQ UQ}.

Lemma Requiv_alt_rw' : Requiv_alt = close.
Proof.
repeat (apply path_forall;intro);apply TruncType.path_iff_ishprop_uncurried.
split.
- apply Requiv_alt_to_Requiv.
- apply Requiv_to_Requiv_alt.
Qed.

Definition Requiv_alt_rw@{}
  := Requiv_alt_rw'@{Ularge Ularge Ularge Ularge}.

Lemma Requiv_rat_rat_def' : forall e q r, close e (rat q) (rat r) = close e q r.
Proof.
rewrite <-Requiv_alt_rw;trivial.
Qed.

Definition Requiv_rat_rat_def@{}
  := Requiv_rat_rat_def'@{Ularge Ularge UQ UQ}.

Lemma Requiv_rat_lim_def' : forall e q y,
  close e (rat q) (lim y) =
  merely (exists d d', e = d + d' /\ close d' (rat q) (y d)).
Proof.
rewrite <-Requiv_alt_rw;trivial.
Qed.

Definition Requiv_rat_lim_def@{}
  := Requiv_rat_lim_def'@{Ularge Ularge UQ UQ}.

Lemma Requiv_lim_rat_def' : forall e x r,
  close e (lim x) (rat r) =
  merely (exists d d', e = d + d' /\ close d' (x d) (rat r)).
Proof.
rewrite <-Requiv_alt_rw;trivial.
Qed.

Definition Requiv_lim_rat_def@{}
  := Requiv_lim_rat_def'@{Ularge Ularge UQ UQ}.

Lemma Requiv_lim_lim_def' : forall e x y,
  close e (lim x) (lim y) =
  merely (exists d d' n, e = d + d' + n /\ close d' (x d) (y n)).
Proof.
rewrite <-Requiv_alt_rw;trivial.
Qed.

Definition Requiv_lim_lim_def@{}
  := Requiv_lim_lim_def'@{Ularge Ularge UQ UQ}.

Lemma Requiv_rounded' : forall {e u v}, close e u v <->
  merely (exists d d', e = d + d' /\ close d u v).
Proof.
rewrite <-Requiv_alt_rw;exact Requiv_alt_round.
Qed.

Definition Requiv_rounded@{} {e u v}
  := @Requiv_rounded'@{UQ} e u v.

Lemma Requiv_triangle' : Triangular Q+ (real Q).
Proof.
hnf;intros. rewrite <-Requiv_alt_rw.
apply Requiv_alt_Requiv with v;trivial.
rewrite Requiv_alt_rw;trivial.
Qed.

Definition Requiv_triangle@{}
  := Requiv_triangle'@{UQ UQ}.

Global Existing Instance Requiv_triangle.

End Requiv_alt.

Lemma two_fourth_is_one_half@{} : @paths Q+ (2/4) (1/2).
Proof. Admitted.

Lemma equiv_through_approx' : forall u (y : Approximation Q) e d,
  close e u (y d) -> close (e+d) u (lim y).
Proof.
apply (real_ind0 (fun u => forall y e d, _ -> _)).
- intros q y e d E.
  rewrite Requiv_rat_lim_def.
  apply tr;do 2 econstructor;split;[|exact E].
  apply qpos_plus_comm.
- intros x Ex y e d xi.
  pose proof (fun e n => Ex n x e n (Requiv_refl _ _)) as E1.
  apply (merely_destruct (fst Requiv_rounded xi)).
  intros [d0 [d' [He E2]]].
  pose proof (Requiv_triangle _ _ _ _ _ (E1 (d' / 2) (d' / 4)) E2) as E3.
  eapply equiv_lim_lim;[|exact E3].
  rewrite He.
  path_via (d0 + (4 / 4) * d' + d).
  { rewrite pos_recip_r,Qpos_mult_1_l. trivial. }
  assert (Hrw : 4 / 4 = 2 / 4 + 1 / 2 :> Q+).
  { rewrite two_fourth_is_one_half. rewrite pos_recip_r;path_via ((2/ 2) : Q+).
    { rewrite pos_recip_r;trivial. }
    { apply (pos_eq Q);ring_tac.ring_with_nat. }
  }
  rewrite Hrw.
  apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Definition equiv_through_approx@{}
  := equiv_through_approx'@{UQ}.

Lemma equiv_lim@{} : forall (x : Approximation Q) e d,
  close (e+d) (x d) (lim x).
Proof.
intros. apply equiv_through_approx.
apply Requiv_refl.
Qed.

Lemma Qpos_lt_min@{} : forall a b : Q+, exists c ca cb, a = c + ca /\ b = c + cb.
Proof.
Admitted.

Lemma unique_continuous_extension@{i} {A:Type@{i} } `{IsHSet A} `{Closeness Q+ A}
  `{forall e, is_mere_relation A (close e)}
  `{!Separated Q+ A} `{!Triangular Q+ A} `{!forall e, Symmetric (close (A:=A) e)}
  `{!Continuous (A:=real Q) (B:=A) f} `{!Continuous (A:=real Q) (B:=A) g}
  : (forall q, f (rat q) = g (rat q)) -> forall u, f u = g u.
Proof.
intros E.
apply (real_ind0 _).
- exact E.
- intros x IHx.
  apply separated.
  intros e.
  apply (merely_destruct (continuous f (lim x) (e/2))).
  intros [d Ed].
  apply (merely_destruct (continuous g (lim x) (e/2))).
  intros [d' Ed'].
  destruct (Qpos_lt_min d d') as [n [nd [nd' [En En']]]].
  assert (Hx : close d (lim x) (x n)).
  { apply Requiv_rounded. apply tr;do 2 econstructor;split;[|
    apply equiv_symm,equiv_lim].
    path_via (nd/2 + n + nd/2).
    path_via (2 / 2 * nd + n).
    { rewrite pos_recip_r,Qpos_mult_1_l,qpos_plus_comm;trivial. }
    apply (pos_eq Q);ring_tac.ring_with_nat.
  }
  assert (Hx' : close d' (lim x) (x n)).
  { apply Requiv_rounded. apply tr;do 2 econstructor;split;[|
    apply equiv_symm,equiv_lim].
    path_via (nd'/2 + n + nd'/2).
    path_via (2 / 2 * nd' + n).
    { rewrite pos_recip_r,Qpos_mult_1_l,qpos_plus_comm;trivial. }
    apply (pos_eq Q);ring_tac.ring_with_nat.
  }
  apply Ed in Hx. apply Ed' in Hx'.
  rewrite IHx in Hx.
  pose proof (triangular Hx (symmetry _ _ Hx')) as E1.
  rewrite (pos_split2 Q e). trivial.
Qed.

Instance R0@{} : Zero (real Q) := rat 0.

Instance R1@{} : One (real Q) := rat 1.

Instance rat_nonexpanding : NonExpanding rat.
Proof.
intros e x y.
apply equiv_rat_rat.
Qed.

Section lipschitz_extend.
Variables (f : Q -> real Q) (L : Q+).
Context {Ef : Lipschitz f L}.

Lemma lipschitz_extend_rat_lim@{} :
  ∀ (q : Q) (d d' e : Q+) (y : Approximation Q) (b : Q+ → real Q)
  (Eb : ∀ d0 e0 : Q+, close (L * (d0 + e0)) (b d0) (b e0)) Eequiv,
  e = d + d'
  → close d' (rat q) (y d)
  → close (L * d') (f q) (b d)
  → close (L * e) (f q)
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / L);
         approx_equiv := Eequiv |}).
Proof.
simpl. intros ???????? He xi IH.
assert (Hrw : L * e = L * d' + L * d)
by (rewrite He;apply (pos_eq Q);ring_tac.ring_with_nat).
rewrite Hrw.
apply equiv_through_approx.
simpl. rewrite (pos_unconjugate Q L d). apply IH.
Qed.

Lemma lipschitz_extend_lim_lim@{} :
  ∀ (x y : Approximation Q) (a b : Q+ → real Q)
  (Ea : ∀ d e : Q+, close (L * (d + e)) (a d) (a e))
  (Eb : ∀ d e : Q+, close (L * (d + e)) (b d) (b e)) (e d n e' : Q+)
  Eequiv1 Eequiv2,
  e = d + n + e'
  → close e' (x d) (y n)
  → close (L * e') (a d) (b n)
  → close (L * e)
      (lim
         {|
         approximate := λ e0 : Q+, a (e0 / L);
         approx_equiv := Eequiv1 |})
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / L);
         approx_equiv := Eequiv2 |}).
Proof.
intros ???????????? He xi IH;simpl.
apply equiv_lim_lim with (L * d) (L * n) (L * e').
+ rewrite He;apply (pos_eq Q);ring_tac.ring_with_nat.
+ simpl. rewrite 2!pos_unconjugate. apply IH.
Qed.

Lemma lipschitz_extend_lim_pr@{} :
  forall (a : Q+ → real Q)
  (Ea : ∀ d e : Q+, close (L * (d + e)) (a d) (a e)),
  ∀ d e : Q+, close (d + e) (a (d / L)) (a (e / L)).
Proof.
intros. pattern (d+e);eapply transport.
apply symmetry, (pos_recip_through_plus Q d e L).
apply Ea.
Qed.

Definition lipshitz_extend_recursor@{}
  : Recursors (real Q) (fun e x y => close (L * e) x y).
Proof.
esplit. Unshelve.
Focus 7.
- exact f.
Focus 7.
- intros _ a Ea.
  apply lim. exists (fun e => a (e / L)).
  apply lipschitz_extend_lim_pr. trivial.
- apply separate_mult.
- apply _.
- intros ???;apply Ef.
- intros ????????;apply lipschitz_extend_rat_lim;trivial.
- simpl;intros ??????? He xi IH.
  apply equiv_symm in xi;apply equiv_symm in IH.
  apply equiv_symm;revert He xi IH;apply lipschitz_extend_rat_lim;trivial.
- simpl. intros ??????????;apply lipschitz_extend_lim_lim;trivial.
Defined.

Definition lipschitz_extend@{}
  : real Q -> real Q
  := real_rec (real Q) (fun e x y => close (L * e) x y)
    lipshitz_extend_recursor.

Global Instance lipschitz_extend_lipschitz@{} : Lipschitz lipschitz_extend L.
Proof.
intros ???;apply (equiv_rec _ _ lipshitz_extend_recursor).
Defined.

Definition lipschitz_extend_rat@{} q : lipschitz_extend (rat q) = f q
  := idpath.

Lemma lipschitz_extend_lim_approx@{} (x : Approximation Q)
  : ∀ d e : Q+, close (d + e) (lipschitz_extend (x (d / L)))
                                 (lipschitz_extend (x (e / L))).
Proof.
exact (lipschitz_extend_lim_pr
                    (λ e : Q+, lipschitz_extend (x e))
                    (λ d e : Q+,
                     equiv_rec (real Q)
                       (λ (e0 : Q+) (x0 y : real Q),
                        close (L * e0) x0 y)
                       lipshitz_extend_recursor (x d) (x e) (d + e)
                       (approx_equiv Q x d e))).
Defined.

Definition lipschitz_extend_lim@{} x
  : lipschitz_extend (lim x) =
    lim (Build_Approximation Q (fun e => lipschitz_extend (x (e / L)))
    (lipschitz_extend_lim_approx x))
  := idpath.

End lipschitz_extend.

Instance lipschitz_extend_nonexpanding (f : Q -> (real Q)) `{!NonExpanding f}
  : NonExpanding (lipschitz_extend f 1).
Proof.
apply (lipschitz_nonexpanding _).
Qed.

Lemma Qclose_neg@{} : forall e (x y : Q), close e x y <-> close e (- x) (- y).
Proof.
Admitted.

Instance Qneg_nonexpanding@{} : NonExpanding ((-) : Negate Q).
Proof.
intros e x y.
apply Qclose_neg.
Defined.

Instance Rneg@{} : Negate (real Q).
Proof.
red. apply (lipschitz_extend (compose rat (-)) _).
Defined.

Instance Rneg_nonexpanding@{} : NonExpanding (@negate (real Q) _).
Proof.
apply _.
Qed.

Lemma Rneg_involutive@{} : forall x : real Q, - - x = x.
Proof.
change (forall x, - - x = id x).
apply unique_continuous_extension;try apply _.
intros;apply (ap rat). apply involutive.
Qed.

Lemma lim_same_distance@{} : forall (x y : Approximation Q) e,
  (forall d n, close (e+d) (x n) (y n)) ->
  forall d, close (e+d) (lim x) (lim y).
Proof.
intros x y e E d.
apply equiv_lim_lim with (d/3) (d/3) (e + d/3);[|apply E].
path_via (e + 3 / 3 * d).
- rewrite pos_recip_r,Qpos_mult_1_l;trivial.
- apply (pos_eq Q);ring_tac.ring_with_nat.
Qed.

Lemma lipschitz_extend_same_distance@{} (f g : Q -> real Q) (L:Q+)
  `{!Lipschitz f L} `{!Lipschitz g L} : forall e,
  (forall d q, close (e+d) (f q) (g q)) ->
  forall d u, close (e+d) (lipschitz_extend f L u) (lipschitz_extend g L u).
Proof.
intros e E1 d u;revert u d;apply (real_ind0 (fun u => forall d, _)).
- intros q d;apply E1.
- intros x Ex d. rewrite !lipschitz_extend_lim.
  apply lim_same_distance. simpl.
  clear d. intros;apply Ex.
Qed.

Section extend_binary.

Definition non_expandingT@{}
  := sigT (fun h : real Q -> real Q => NonExpanding h).

Instance non_expanding_close@{} : Closeness Q+ non_expandingT
  := fun e h k => forall u, close e (h.1 u) (k.1 u).

Definition non_expanding_separated@{} : forall h k : non_expandingT,
  (forall e, close e h k) -> h = k.
Proof.
intros h k E. unfold non_expandingT,NonExpanding. apply Sigma.path_sigma_hprop.
apply path_forall;intros x. apply equiv_path;intro e.
exact (E _ _).
Qed.

Variable (f : Q -> Q -> Q).
Context {Hfl : forall s, NonExpanding (fun q => f q s)}
  {Hfr : forall q, NonExpanding (f q)}.

Lemma non_expanding_approx_pr@{} (a : Q+ → non_expandingT)
  (Ea : ∀ d e : Q+, non_expanding_close (d + e) (a d) (a e))
  (v : real Q) (d e : Q+)
  : close (d + e) ((a d).1 v) ((a e).1 v).
Proof.
apply Ea.
Qed.

Lemma lim_is_non_expanding@{} :
forall (a : Q+ → non_expandingT)
(Ea : ∀ d e : Q+, non_expanding_close (d + e) (a d) (a e))
(e : Q+) (u v : real Q),
close e u v
→ close e
    (lim
       {|
       approximate := λ e0 : Q+, (a (e0/2)).1 u;
       approx_equiv := non_expanding_approx_pr a Ea u |})
    (lim
       {|
       approximate := λ e0 : Q+, (a (e0/2)).1 v;
       approx_equiv := non_expanding_approx_pr a Ea v |}).
Proof.
intros a Ea e u v E1.
generalize (fst Requiv_rounded E1).
apply (Trunc_ind _);intros [d [d' [He E2]]].
apply equiv_lim_lim with (d'/2) (d'/2) d.
- rewrite He.
  path_via (d + (2/2) * d').
  { rewrite pos_recip_r,Qpos_mult_1_l;trivial. }
  apply (pos_eq Q);ring_tac.ring_with_nat.
- simpl. apply ((a _).2). trivial.
Qed.

Lemma rat_non_expanding_pr@{} :
∀ q (e : Q+) (u v : real Q),
close e u v
→ close e (lipschitz_extend (rat ∘ f q) 1 u)
    (lipschitz_extend (rat ∘ f q) 1 v).
Proof.
intro;apply non_expanding. apply lipschitz_extend_nonexpanding.
Qed.

Lemma non_expanding_rat_rat_pr@{} :
∀ (q r : Q) (e : Q+),
- ' e < q - r < ' e
→ non_expanding_close e
    (lipschitz_extend (rat ∘ f q) 1 ↾ rat_non_expanding_pr q)
    (lipschitz_extend (rat ∘ f r) 1 ↾ rat_non_expanding_pr r).
Proof.
red. simpl. intros q r e He.
apply Qclose_rounded in He.
apply (merely_destruct He);clear He;intros [d [d' [He E1]]].
rewrite He. apply lipschitz_extend_same_distance.
intros n s;apply (nonexpanding_compose rat (fun q => f q s)).
apply Qclose_rounded.
apply tr;exists d,n;auto.
Qed.

Lemma non_expanding_rat_lim_pr@{} :
∀ (q : Q) (d d' e : Q+) (y : Approximation Q) (b : Q+ → non_expandingT)
(Eb : ∀ d0 e0 : Q+, non_expanding_close (d0 + e0) (b d0) (b e0)),
e = d + d'
→ close d' (rat q) (y d)
  → non_expanding_close d'
      (lipschitz_extend (rat ∘ f q) 1 ↾ rat_non_expanding_pr q) (b d)
    → non_expanding_close e
        (lipschitz_extend (rat ∘ f q) 1 ↾ rat_non_expanding_pr q)
        ((λ v : real Q,
          lim
            {|
            approximate := λ e0 : Q+, (b e0).1 v;
            approx_equiv := non_expanding_approx_pr b Eb v |})
         ↾ lim_is_non_expanding b Eb).
Proof.
intros q d d' e y b Eb He xi IH.
hnf. intros u;simpl.
rewrite He,qpos_plus_comm. apply equiv_through_approx.
simpl. hnf in IH. apply IH.
Qed.

Lemma non_expanding_lim_rat_pr@{} :
∀ (r : Q) (d d' e : Q+) (x : Approximation Q) (a : Q+ → non_expandingT)
(Ea : ∀ d0 e0 : Q+, non_expanding_close (d0 + e0) (a d0) (a e0)),
e = d + d'
→ close d' (x d) (rat r)
  → non_expanding_close d' (a d)
      (lipschitz_extend (rat ∘ f r) 1 ↾ rat_non_expanding_pr r)
    → non_expanding_close e
        ((λ v : real Q,
          lim
            {|
            approximate := λ e0 : Q+, (a e0).1 v;
            approx_equiv := non_expanding_approx_pr a Ea v |})
         ↾ lim_is_non_expanding a Ea)
        (lipschitz_extend (rat ∘ f r) 1 ↾ rat_non_expanding_pr r).
Proof.
intros r d d' e x a Ea He xi IH u;simpl.
apply equiv_symm.
rewrite He,qpos_plus_comm;apply equiv_through_approx,equiv_symm.
apply IH.
Qed.

Lemma non_expanding_lim_lim_pr@{} :
∀ (x y : Approximation Q) (a b : Q+ → non_expandingT)
(Ea : ∀ d e : Q+, non_expanding_close (d + e) (a d) (a e))
(Eb : ∀ d e : Q+, non_expanding_close (d + e) (b d) (b e)) (e d n e' : Q+),
e = d + n + e'
→ close e' (x d) (y n)
  → non_expanding_close e' (a d) (b n)
    → non_expanding_close e
        ((λ v : real Q,
          lim
            {|
            approximate := λ e0 : Q+, (a e0).1 v;
            approx_equiv := non_expanding_approx_pr a Ea v |})
         ↾ lim_is_non_expanding a Ea)
        ((λ v : real Q,
          lim
            {|
            approximate := λ e0 : Q+, (b e0).1 v;
            approx_equiv := non_expanding_approx_pr b Eb v |})
         ↾ lim_is_non_expanding b Eb).
Proof.
intros x y a b Ea Eb e d n e' He xi IH u;simpl.
eapply equiv_lim_lim;[|apply IH]. trivial.
Qed.

Definition non_expanding_recursor@{} : Recursors non_expandingT non_expanding_close.
Proof.
simple refine (Build_Recursors non_expandingT non_expanding_close
  _ _
  non_expanding_separated _
  _ _ _ _).
- intros q. exists (lipschitz_extend (compose rat (f q)) 1).
  exact (rat_non_expanding_pr q).
- intros x a Ea.
  simple refine (exist _ _ _).
  + intros v;apply lim. exists (fun e => (a e).1 v).
    exact (non_expanding_approx_pr a Ea v).
  + simpl. exact (lim_is_non_expanding a Ea).
- exact non_expanding_rat_rat_pr. 
- exact non_expanding_rat_lim_pr.
- exact non_expanding_lim_rat_pr.
- exact non_expanding_lim_lim_pr.
Defined.

Definition non_expanding_extend@{} : real Q -> real Q -> real Q
  := fun u => (real_rec _ _ non_expanding_recursor u).1.

Global Instance non_expanding_extend_close_l@{}
  : forall w, NonExpanding (fun u => non_expanding_extend u w).
Proof.
intros w e u v xi.
apply (equiv_rec _ _ non_expanding_recursor _ _ _ xi).
Qed.

Global Instance non_expanding_extend_close_r@{}
  : forall u, NonExpanding (non_expanding_extend u).
Proof.
intros u.
apply ((real_rec _ _ non_expanding_recursor u).2).
Qed.

Definition non_expanding_extend_rat@{} q v :
  non_expanding_extend (rat q) v =
  lipschitz_extend (compose rat (f q)) 1 v
  := idpath.

Definition non_expanding_extend_lim_pr@{} (x : Approximation Q) v
  : ∀ d e : Q+,
    close (d + e) (non_expanding_extend (x d) v)
      (non_expanding_extend (x e) v)
  :=
  non_expanding_approx_pr
    (λ e : Q+,
     real_rec non_expandingT non_expanding_close
       non_expanding_recursor (x e))
    (λ d e : Q+,
     equiv_rec non_expandingT non_expanding_close
       non_expanding_recursor (x d) (x e) (d + e)
       (approx_equiv Q x d e)) v.

Definition non_expanding_extend_lim@{} x v :
  non_expanding_extend (lim x) v =
  lim (Build_Approximation Q
    (fun e => non_expanding_extend (x e) v) (non_expanding_extend_lim_pr x v))
  := idpath.

Definition non_expanding_extend_rat_rat@{} q r :
  non_expanding_extend (rat q) (rat r) = rat (f q r)
  := idpath.

End extend_binary.

Instance Qplus_nonexpanding_l@{} : forall s : Q, NonExpanding (+ s).
Proof.
red. unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : q + s - (r + s) = q - r);[|rewrite Hrw;trivial].
rewrite negate_plus_distr. path_via (q - r + (s - s)).
- ring_tac.ring_with_nat.
- rewrite plus_negate_r;apply plus_0_r.
Qed.

Instance Qplus_nonexpanding_r@{} : forall s : Q, NonExpanding (s +).
Proof.
red;unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : s + q - (s + r) = q - r);[|rewrite Hrw;trivial].
rewrite negate_plus_distr. path_via (q - r + (s - s)).
- ring_tac.ring_with_nat.
- rewrite plus_negate_r;apply plus_0_r.
Qed.

Global Instance Rplus@{} : Plus (real Q) := non_expanding_extend plus.

Definition Rplus_rat_rat@{} q r : rat q + rat r = rat (q + r)
  := idpath.

Global Instance Rplus_nonexpanding_l@{} : forall s : real Q, NonExpanding (+ s)
  := _.
Global Instance Rplus_nonexpanding_r@{} : forall s : real Q, NonExpanding (s +)
  := _.

Lemma unique_continuous_binary_extension@{} {f : real Q -> real Q -> real Q}
  `{forall x, Continuous (f x)} `{forall y, Continuous (fun x => f x y)}
  {g : real Q -> real Q -> real Q}
  `{forall x, Continuous (g x)} `{forall y, Continuous (fun x => g x y)}
  : (forall q r, f (rat q) (rat r) = g (rat q) (rat r)) ->
  forall u v, f u v = g u v.
Proof.
intros E.
intros x;apply unique_continuous_extension;try apply _.
intros r;revert x;apply unique_continuous_extension;try apply _.
trivial.
Qed.

Lemma unique_continuous_ternary_extension@{} {f}
  `{forall x y, Continuous (f x y)} `{forall x z, Continuous (fun y => f x y z)}
  `{forall y z, Continuous (fun x => f x y z)}
  {g}
  `{forall x y, Continuous (g x y)} `{forall x z, Continuous (fun y => g x y z)}
  `{forall y z, Continuous (fun x => g x y z)}
  : (forall q r s, f (rat q) (rat r) (rat s) = g (rat q) (rat r) (rat s)) ->
  forall u v w, f u v w = g u v w.
Proof.
intros E u;apply unique_continuous_binary_extension.
intros q r;revert u;apply unique_continuous_extension;try apply _.
auto.
Qed.

Instance Rplus_comm@{} : Commutative (@plus _ Rplus).
Proof.
hnf. apply unique_continuous_binary_extension.
intros q r;apply (ap rat),plus_comm.
Qed.

Lemma Rplus_assoc@{} : Associative (@plus _ Rplus).
Proof.
hnf. intros x;apply @unique_continuous_binary_extension.
{ apply _. }
{ apply _. }
{ apply _. }
{ change (forall y, Continuous (compose (+ y) (x +))).
  apply _. }
intros r s;revert x;eapply @unique_continuous_extension;try apply _.
{ change (Continuous (compose (+ rat s) (+ rat r))). apply _. }
intros q;apply (ap rat),plus_assoc.
Qed.

Instance lipschitz_const@{} : forall (a:real Q) (L:Q+), Lipschitz (fun _ => a) L.
Proof.
intros;hnf.
intros e _ _ _. apply Requiv_refl.
Qed.

Lemma lipschitz_dup@{} (f : real Q -> real Q -> real Q) (L1 L2 : Q+)
  `{!forall x, Lipschitz (f x) L1} `{!forall y, Lipschitz (fun x => f x y) L2}
  : Lipschitz (fun x => f x x) (L1 + L2).
Proof.
hnf. intros e x y xi.
assert (Hrw : (L1 + L2) * e = L1 * e + L2 * e)
by (apply (pos_eq Q);ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply (Requiv_triangle _ (f x y)).
- apply (lipschitz _ _ xi).
- apply (lipschitz (fun x => f x y) _ xi).
Qed.

Instance Rplus_group@{} : Group (real Q).
Proof.
repeat split.
- apply _.
- exact Rplus_assoc.
- hnf. change mon_unit with 0.
  change sg_op with plus.
  apply unique_continuous_extension;try apply _.
  intros;apply (ap rat);apply plus_0_l.
- hnf. change mon_unit with 0.
  change sg_op with plus.
  apply unique_continuous_extension;try apply _.
  intros;apply (ap rat);apply plus_0_r.
- hnf; change mon_unit with 0.
  change sg_op with plus.
  eapply @unique_continuous_extension;try apply _.
  { eapply lipschitz_continuous;try apply _.
    apply (@lipschitz_dup (fun a b => - a + b) 1 1).
    { apply _. }
    { change (forall y, Lipschitz (compose (+ y) (-)) (1:Q+)). apply _. } 
  }
  intros;apply (ap rat),plus_negate_l.
- hnf; change mon_unit with 0.
  change sg_op with plus.
  eapply @unique_continuous_extension;try apply _.
  { eapply lipschitz_continuous;try apply _.
    apply (@lipschitz_dup (fun a b => a - b) 1 1).
    { change (forall x, Lipschitz (compose (x +) (-)) (1:Q+)). apply _. }
    { apply _. } 
  }
  intros;apply (ap rat),plus_negate_r.
Unshelve. all:exact 1.
Qed.

Instance Qmeet_nonexpanding_l : forall s : Q, NonExpanding (⊓ s).
Proof.
Admitted.

Instance Qmeet_nonexpanding_r : forall s : Q, NonExpanding (s ⊓).
Proof.
Admitted.

Global Instance Rmeet@{} : Meet (real Q) := non_expanding_extend meet.

Global Instance Rmeet_lipschitz_l@{} : forall s : real Q, NonExpanding (⊓ s)
  := _.
Global Instance Rmeet_lipschitz_r@{} : forall s : real Q, NonExpanding (s ⊓)
  := _.

Definition Rmeet_rat_rat@{} q r : meet (rat q) (rat r) = rat (meet q r)
  := idpath.

Instance Qjoin_lipschitz_l : forall s : Q, NonExpanding (⊔ s).
Proof. Admitted.
Instance Qjoin_lipschitz_r : forall s : Q, NonExpanding (s ⊔).
Proof. Admitted.

Global Instance Rjoin@{} : Join (real Q) := non_expanding_extend join.

Global Instance Rjoin_lipschitz_l@{} : forall s : real Q, NonExpanding (⊔ s)
  := _.
Global Instance Rjoin_lipschitz_r@{} : forall s : real Q, NonExpanding (s ⊔)
  := _.

Definition Rjoin_rat_rat@{} q r : join (rat q) (rat r) = rat (join q r)
  := idpath.

Global Instance Rle@{} : Le (real Q) := fun x y => join x y = y.
Arguments Rle _ _ /.

Global Instance Rlt@{} : Lt (real Q) := fun x y =>
  merely (exists q r, x <= (rat q) /\ q < r /\ (rat r) <= y).
Arguments Rlt _ _ /.

Global Instance Rap@{} : Apart@{UQ UQ} (real Q) := fun x y => x < y \/ y < x.
Arguments Rap _ _ /.

Instance Rle_trans@{} : Transitive Rle.
Proof.
hnf. unfold le,Rle.
intros x y z E1 E2. rewrite <-E2,<-E1. clear E1 E2;revert x.
eapply @unique_continuous_extension;try apply _.
{ eapply @lipschitz_continuous;try apply _.
  eapply (@lipschitz_dup (fun u v => u ⊔ ((v ⊔ y) ⊔ z))).
  { intros u. apply nonexpanding_lipschitz.
    change (NonExpanding (compose (u ⊔) (compose (⊔ z) (⊔ y)))).
    apply _. }
  { intros u. apply nonexpanding_lipschitz.
    apply _. }
}
{ eapply @nonexpanding_continuous;try apply _.
  change (NonExpanding (compose (⊔ z) (⊔ y)));apply _. }
intros q;revert y z.
apply @unique_continuous_binary_extension.
{ intros x;eapply nonexpanding_continuous;try apply _. }
{ intros y;eapply nonexpanding_continuous;try apply _.
  change (NonExpanding (compose (rat q ⊔) (compose (⊔ y) (rat q ⊔))));apply _.
}
{ intros x;eapply nonexpanding_continuous;apply _. }
{ intros y;eapply nonexpanding_continuous;try apply _.
  change (NonExpanding (compose (⊔ y) (rat q ⊔)));apply _.
}
intros r s.
apply (ap rat).
apply join_r. apply join_le_compat_r,join_ub_l.
Qed.

Instance Rle_refl@{} : Reflexive Rle.
Proof.
change (forall x, join x x = x).
eapply @unique_continuous_extension;try apply _.
+ eapply lipschitz_continuous;try apply _. apply lipschitz_dup;apply _.
+ intros;apply (ap rat),semilattice_idempotent,join_sl_order_join_sl.
Qed.

Lemma real_eq_equiv@{} : forall u v : real Q, u = v -> forall e, close e u v.
Proof.
intros u v [] e;apply Requiv_refl.
Qed.

Lemma rat_injective' : Injective rat.
Proof.
intros q r E.
apply Qclose_separating.
intros e. rewrite <-Requiv_rat_rat_def.
apply real_eq_equiv. trivial.
Qed.

Instance rat_injective@{} : Injective rat
  := rat_injective'@{UQ}.

Instance Rlt_irrefl@{} : Irreflexive Rlt.
Proof.
hnf. intros x;hnf;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
pose proof (transitivity E3 E1) as E4.
hnf in E4. apply rat_injective in E4.
revert E2;apply le_iff_not_lt_flip. rewrite <-E4.
apply join_ub_l.
Qed.

Instance rat_le_reflecting : OrderReflecting rat.
Proof.
hnf. intros q r E;unfold le,Rle in E.
apply rat_injective in E. rewrite <-E;apply join_ub_l.
Qed.

Instance rat_le_preserve : OrderPreserving rat.
Proof.
hnf. intros q r E;hnf.
apply (ap rat). apply join_r,E.
Qed.

Instance Rlt_trans@{} : Transitive Rlt.
Proof.
intros a b c.
unfold Rlt.
apply (Trunc_ind (fun _ => _ -> _));intros [q1 [r1 [E1 [E2 E3]]]];
apply (Trunc_ind _);intros [q2 [r2 [E4 [E5 E6]]]].
apply tr. exists q1,r2. split;[|split];trivial.
pose proof (rat_le_reflecting _ _ (transitivity E3 E4)) as E7.
apply lt_le_trans with r1;trivial.
apply lt_le. apply le_lt_trans with q2;trivial.
Qed.

Instance Rapart_ishprop : forall x y : real Q, IsHProp (apart x y).
Proof.
unfold apart;simpl. intros x y.
apply Sum.ishprop_sum;try apply _.
intros E1 E2.
apply (irreflexivity lt x). transitivity y;trivial.
Qed.

Lemma Q_average_between@{} : forall q r : Q, q < r -> q < (q + r) / 2 < r.
Proof.
Admitted.

Lemma Q_dense@{} : forall q r : Q, q < r -> exists s, q < s < r.
Proof.
intros q r E;econstructor;apply Q_average_between,E.
Qed.

Lemma R_le_lt_trans@{} : forall a b c : real Q, a <= b -> b < c -> a < c.
Proof.
intros a b c E1;apply (Trunc_ind _);intros [q [r [E2 [E3 E4]]]].
apply tr;exists q,r;auto.
Qed.

Lemma R_lt_le_trans@{} : forall a b c : real Q, a < b -> b <= c -> a < c.
Proof.
intros a b c E0 E1;revert E0;apply (Trunc_ind _);intros [q [r [E2 [E3 E4]]]].
apply tr;exists q,r;auto.
Qed.

Instance rat_lt_preserving@{} : StrictlyOrderPreserving rat.
Proof.
hnf. intros x y E.
hnf. apply tr;exists x,y;repeat split;auto.
Qed.

Lemma R_lt_le@{} : forall a b : real Q, a < b -> a <= b.
Proof.
intros a b;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
transitivity (rat q);trivial.
transitivity (rat r);trivial.
apply rat_le_preserve. apply lt_le. trivial.
Qed.

Lemma rat_lt_reflecting@{} : StrictlyOrderReflecting rat.
Proof.
hnf. intros x y;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply (order_reflecting rat) in E1;apply (order_reflecting rat) in E3.
apply le_lt_trans with q;trivial.
apply lt_le_trans with r;trivial.
Qed.

Lemma R_archimedean@{} : forall u v, u < v -> merely (exists q, u < rat q < v).
Proof.
intros u v;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply tr;exists ((q+r)/2).
split.
- apply R_le_lt_trans with (rat q);trivial.
  apply rat_lt_preserving. apply Q_average_between. exact E2.
- apply R_lt_le_trans with (rat r);trivial.
  apply rat_lt_preserving. apply Q_average_between. exact E2.
Qed.

Lemma Rle_close_rat_rat' : forall q r, r <= q -> forall v e, close e (rat r) v ->
  v <= rat (q + ' e).
Proof.
intros q r E.
apply (real_ind0 (fun v => forall e, _ -> _)).
+ intros s e E'.
  rewrite Requiv_rat_rat_def in E'.
  hnf in E'. apply (order_preserving rat).
  apply lt_le. rewrite plus_comm. apply flip_lt_minus_l.
  apply le_lt_trans with (s - r).
  * apply plus_le_compat;[reflexivity|].
    apply (snd (flip_le_negate _ _)),E.
  * apply flip_lt_negate. rewrite <-negate_swap_r. apply E'.
+ intros y IH e xi.
  apply Requiv_rounded in xi.
  revert xi;apply (Trunc_ind _);intros [d [d' [He xi]]].
  hnf. unfold join,Rjoin. rewrite non_expanding_extend_lim.
  change (non_expanding_extend join) with join.
  assert (E1 : forall n n', d' = n + n' -> y n <= rat (q + ' e)).
  { intros n n' Hd.
    apply IH. rewrite He. apply @Requiv_triangle with (lim y);trivial.
    apply equiv_symm. rewrite Hd,qpos_plus_comm. apply equiv_lim.
  }
  apply equiv_path. intros z.
  destruct (Qpos_lt_min z d') as [a [ca [cb [E2 E3]]]].
  eapply equiv_lim_rat;[|simpl;erewrite E1;[apply Requiv_refl|]].
  * exact E2.
  * exact E3.
Qed.

Definition Rle_close_rat_rat@{}
  := Rle_close_rat_rat'@{UQ}.

Instance Rjoin_comm@{} : Commutative (@join _ Rjoin).
Proof.
hnf. apply unique_continuous_binary_extension.
intros;apply (ap rat).
apply join_sl_order_join_sl.
Qed.

Local Existing Instance lattice_order_lattice.

Lemma R_lattice' : LatticeOrder Rle.
Proof.
split.
- apply @alt_Build_MeetSemiLatticeOrder;[
  repeat split;unfold sg_op,meet_is_sg_op;change Rmeet with meet
  |apply _|].
  + apply _.
  + hnf.
    apply @unique_continuous_ternary_extension;try apply _.
    { change (forall x z, Continuous (compose (⊓ z) (x ⊓)));apply _. }
    { change (forall y z, Continuous (compose (⊓ z) (⊓ y)));apply _. }
    intros;apply (ap rat). apply associativity.
  + hnf.
    apply unique_continuous_binary_extension.
    intros;apply (ap rat). apply commutativity.
  + hnf. red.
    eapply @unique_continuous_extension;try apply _.
    { eapply @lipschitz_continuous;try apply _. apply lipschitz_dup;apply _. }
    intros;apply (ap rat),idempotency,_.
  + unfold le,Rle. intros x y;split;intros E.
    * rewrite <-E.
      clear E;revert x y;apply @unique_continuous_binary_extension;try apply _.
      { intros;eapply @lipschitz_continuous;try apply _.
        apply (lipschitz_dup (fun x1 x2 => x1 ⊓ (x2 ⊔ y)));apply _. }
      intros;apply (ap rat). apply (meet_join_absorption _).
    * rewrite <-E.
      clear E;revert x y;apply @unique_continuous_binary_extension;try apply _.
      { intros;eapply @lipschitz_continuous;try apply _.
        apply (lipschitz_dup (fun v1 v2 => (x ⊓ v1) ⊔ v2));try apply _.
        intro;apply nonexpanding_lipschitz.
        change (NonExpanding (compose (⊔ y) (x ⊓)));apply _.
      }
      { change (forall y, Continuous (compose (⊔ y) (⊓ y)));apply _. }
      intros;apply (ap rat).
      rewrite (commutativity (f:=join)),(commutativity (f:=meet)).
      apply (join_meet_absorption _).
- apply @alt_Build_JoinSemiLatticeOrder;[|apply _|reflexivity].
  repeat split;unfold sg_op,join_is_sg_op;change Rjoin with join.
  + apply _.
  + hnf.
    apply @unique_continuous_ternary_extension;try apply _.
    { change (forall x z, Continuous (compose (⊔ z) (x ⊔)));apply _. }
    { change (forall y z, Continuous (compose (⊔ z) (⊔ y)));apply _. }
    intros;apply (ap rat). apply associativity.
  + hnf.
    apply unique_continuous_binary_extension.
    intros;apply (ap rat). apply commutativity.
  + hnf. red.
    eapply @unique_continuous_extension;try apply _.
    { eapply @lipschitz_continuous;try apply _. apply lipschitz_dup;apply _. }
    intros;apply (ap rat),idempotency,_.
Unshelve. all:exact 1.
Qed.

Instance R_lattice@{} : LatticeOrder Rle
  := R_lattice'@{Ularge UQ}.

Lemma Rle_close_rat@{} : forall q u, u <= rat q -> forall v e, close e u v ->
  v <= rat (q + ' e).
Proof.
intros q u E v e xi.
pose proof (non_expanding (join (rat q)) xi) as E1.
hnf in E. rewrite Rjoin_comm in E1.
rewrite E in E1.
pose proof (Rle_close_rat_rat q q (reflexivity q) _ _ E1) as E2.
transitivity (join (rat q) v);trivial.
apply join_ub_r.
Qed.

Lemma Rlt_close_rat_plus@{} : forall u q, u < rat q ->
  forall v e, close e u v -> v < rat (q + ' e).
Proof.
intros u q;apply (Trunc_ind (fun _ => forall v e, _ -> _)).
intros [q' [r [E1 [E2 E3]]]] v e xi.
hnf. apply tr. exists (q' + ' e),(r + ' e).
split;[|split].
- apply Rle_close_rat with u;trivial.
- apply plus_lt_le_compat;[|reflexivity].
  trivial.
- apply (order_preserving rat).
  apply plus_le_compat;[|reflexivity].
  apply (order_reflecting rat);trivial.
Qed.

Lemma Rlt_close_exists_aux@{} : forall u q, u < rat q ->
  merely (exists e, forall v, close e u v -> v < rat q).
Proof.
intros u q;apply (Trunc_ind _);intros [q' [r [E1 [E2 E3]]]].
transparent assert (rq : Q+).
{ exists (r-q').
  abstract (apply flip_pos_minus in E2; trivial).
}
apply tr;exists (rq / 2);intros v xi.
pose proof (Rle_close_rat _ _ E1 _ _ xi) as E4.
change (v <= rat (q' + (r - q') / 2)) in E4.
apply tr;econstructor;exists r;repeat split;eauto.
apply flip_pos_minus. rewrite negate_plus_distr.
rewrite negate_mult_distr_l,<-negate_swap_l.
assert (Hrw : r + (- q' + (- r + q') / 2) = (r - q') / 2).
{ path_via (2 / 2 * r + (2 / 2 * (- q') + (- r + q') / 2)).
  { rewrite dec_recip_inverse;[|solve_propholds].
    rewrite !mult_1_l;trivial. }
  path_via ((r - q' + (r - r) + (q' - q')) / 2).
  { ring_tac.ring_with_nat. }
  rewrite !plus_negate_r,!plus_0_r;trivial.
}
rewrite Hrw.
apply pos_mult_compat;[|apply _].
apply (snd (flip_pos_minus _ _)). trivial.
Qed.

Lemma Rlt_close_exists@{} : forall u v, u < v ->
  merely (exists e, forall w, close e u w -> w < v).
Proof.
intros u v;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
generalize (Rlt_close_exists_aux u r
  (R_le_lt_trans _ _ _ E1 (rat_lt_preserving _ _ E2))).
apply (Trunc_ind _);intros [e E4];apply tr;exists e.
intros w xi;apply R_lt_le_trans with (rat r);auto.
Qed.

Instance Qabs_nonexpanding : NonExpanding (abs (A:=Q)).
Proof.
Admitted.

Definition Rabs_val := lipschitz_extend (compose rat abs) 1.

Global Instance Rabs_nonexpanding : NonExpanding Rabs_val := _.

Lemma Rabs_of_nonneg' : forall x, 0 <= x -> Rabs_val x = x.
Proof.
unfold le;simpl. intros x E;rewrite <-E.
clear E;revert x;apply unique_continuous_extension;try apply _.
intros q;apply (ap rat).
apply ((abs_sig _).2). apply join_ub_l.
Qed.

Lemma Rabs_of_nonpos' : forall x, x <= 0 -> Rabs_val x = - x.
Proof.
intros x E.
apply meet_l in E. rewrite <-E.
clear E;revert x;apply unique_continuous_extension;try apply _.
intros q;apply (ap rat).
apply ((abs_sig _).2). apply meet_lb_r.
Qed.

Instance Rabs : Abs (real Q).
Proof.
intros u. exists (Rabs_val u).
split.
- apply Rabs_of_nonneg'.
- apply Rabs_of_nonpos'.
Defined.

Lemma Rabs_of_nonneg@{} : forall x : real Q, 0 <= x -> abs x = x.
Proof.
intros x;apply ((abs_sig x).2).
Qed.

Lemma Rabs_of_nonpos : forall x : real Q, x <= 0 -> abs x = - x.
Proof.
intros x;apply ((abs_sig x).2).
Qed.

Lemma Rabs_of_0 : abs (A:=real Q) 0 = 0.
Proof.
apply Rabs_of_nonneg;reflexivity.
Qed.

Lemma Rabs_of_0' : forall x : real Q, x = 0 -> abs x = 0.
Proof.
intros x E;rewrite E;apply Rabs_of_0.
Qed.

Lemma total_abs_either `{Abs A} `{!TotalRelation le}
  : forall x : A, (0 <= x /\ abs x = x) \/ (x <= 0 /\ abs x = - x).
Proof.
intros x.
destruct (total le 0 x) as [E|E].
- left. split;trivial. apply ((abs_sig x).2);trivial.
- right. split;trivial. apply ((abs_sig x).2);trivial.
Qed.

Lemma Qabs_nonneg@{} : forall q : Q, 0 <= abs q.
Proof.
intros q;destruct (total_abs_either q) as [E|E];destruct E as [E1 E2];rewrite E2.
- trivial.
- apply flip_nonneg_negate. rewrite involutive;trivial.
Qed.

Lemma Rabs_nonneg@{} : forall x : real Q, 0 <= abs x.
Proof.
unfold le;simpl. apply unique_continuous_extension;try apply _.
intros;apply (ap rat).
apply join_r. apply Qabs_nonneg.
Qed.

Instance Rabs_idempotent@{} : UnaryIdempotent (abs (A:=real Q)).
Proof.
hnf. apply path_forall. intros x. unfold compose.
apply Rabs_of_nonneg, Rabs_nonneg.
Qed.

Lemma equiv_0_metric' : forall e u, close e u 0 -> abs u < rat (' e).
Proof.
intros e u;revert u e;apply (real_ind0 (fun u => forall e, _ -> _)).
- intros q e E.
  rewrite Requiv_rat_rat_def in E.
  hnf in E. rewrite negate_0,plus_0_r in E.
  apply rat_lt_preserving.
  destruct (total_abs_either q) as [[_ E']|[_ E']];rewrite E'.
  + apply E.
  + apply flip_lt_negate. rewrite involutive. apply E.
- intros x IH e xi.
  generalize (fst Requiv_rounded xi). apply (Trunc_ind _);intros [d [d' [He xi']]].
  rewrite Requiv_lim_rat_def in xi'.
  revert xi';apply (Trunc_ind _);intros [n [n' [Hd E1]]].
  apply IH in E1.
  rewrite He,Hd.
  assert (Hrw : (' (n + n' + d')) = ' n' + ' (n + d'))
  by ring_tac.ring_with_nat.
  rewrite Hrw;clear Hrw.
  apply (Rlt_close_rat_plus _ _ E1).
  apply (non_expanding abs).
  rewrite qpos_plus_comm. apply equiv_lim.
Qed.

Definition equiv_0_metric@{}
  := equiv_0_metric'@{UQ UQ}.

Lemma equiv_to_metric@{} : forall e u v, close e u v -> abs (u - v) < rat (' e).
Proof.
intros e u v xi.
rewrite <-Rabs_idempotent.
apply equiv_0_metric.
rewrite <-(Rabs_of_0' (u - u));[|apply right_inverse].
apply (non_expanding (fun w => abs (u - w))).
apply equiv_symm,xi.
Qed.

Lemma Qclose_alt : forall e (q r : Q), close e q r <-> abs (q - r) < ' e.
Proof. Admitted.

Lemma metric_to_equiv_rat_lim@{} (q : Q)
  (y : Approximation Q)
  (IHy : ∀ e e0 : Q+, abs (rat q - y e) < rat (' e0) → close e0 (rat q) (y e))
  (e : Q+)
  (E1 : abs (rat q - lim y) < rat (' e))
  : close e (rat q) (lim y).
Proof.
generalize (R_archimedean _ _ E1). apply (Trunc_ind _);intros [d [E2 E3]].
apply rat_lt_reflecting in E3.
pose proof (snd (flip_pos_minus _ _) E3) as E4.
assert (Hd : 0 < d).
{ revert E2;apply (Trunc_ind _).
  intros [s [s' [F1 [F2 F3]]]].
  apply rat_le_reflecting in F3.
  apply lt_le_trans with s';trivial.
  apply le_lt_trans with s;trivial.
  apply rat_le_reflecting.
  transitivity (abs (rat q - lim y));trivial.
  apply Rabs_nonneg.
}
pose (D := mkQpos Q d Hd).
pose (ED := mkQpos Q _ E4).
assert (Hrw : e = D + (ED / 4 + ED / 4) + (ED / 4 + ED / 4)).
{ path_via (D + ED).
  { apply (pos_eq Q);unfold D, ED.
    change (' e = d + (' e - d)).
    path_via ('e + (d - d));[|ring_tac.ring_with_nat].
    rewrite plus_negate_r,plus_0_r;trivial.
  }
  path_via (D + 4 / 4 * ED).
  { rewrite pos_recip_r,Qpos_mult_1_l;trivial. }
  apply (pos_eq Q);ring_tac.ring_with_nat.
}
rewrite Hrw.
eapply Requiv_triangle;[|apply equiv_lim].
apply IHy. apply (Rlt_close_rat_plus _ _ E2).
apply (non_expanding (fun u => abs (rat q - u))).
apply equiv_symm,equiv_lim.
Qed.

Lemma Qabs_neg_flip@{} : forall a b : Q, abs (a - b) = abs (b - a).
Proof.
intros a b. unfold abs.
destruct (total le 0 (a - b)) as [E|E].
- rewrite (fst (abs_sig (a-b)).2 E).
  rewrite (snd (abs_sig (b-a)).2).
  + apply negate_swap_r.
  + apply flip_nonpos_negate. rewrite <-negate_swap_r;trivial.
- rewrite (snd (abs_sig (a-b)).2 E).
  rewrite (fst (abs_sig (b-a)).2).
  + Symmetry;apply negate_swap_r.
  + apply flip_nonneg_negate. rewrite <-negate_swap_r;trivial.
Qed.

Lemma Rabs_neg_flip@{} : forall a b : real Q, abs (a - b) = abs (b - a).
Proof.
apply unique_continuous_binary_extension.
intros q r;apply (ap rat).
apply Qabs_neg_flip.
Qed.

Lemma metric_to_equiv_lim_lim@{} (x : Approximation Q)
  (IHx : ∀ (e : Q+) (v : real Q) (e0 : Q+),
        abs (x e - v) < rat (' e0) → close e0 (x e) v)
  (y : Approximation Q)
  (IHy : ∀ e e0 : Q+, abs (lim x - y e) < rat (' e0) → close e0 (lim x) (y e))
  (e : Q+)
  (E1 : abs (lim x - lim y) < rat (' e))
  : close e (lim x) (lim y).
Proof.
generalize (R_archimedean _ _ E1). apply (Trunc_ind _);intros [d [E2 E3]].
apply rat_lt_reflecting in E3.
pose proof (snd (flip_pos_minus _ _) E3) as E4.
assert (Hd : 0 < d).
{ revert E2;apply (Trunc_ind _).
  intros [s [s' [F1 [F2 F3]]]].
  apply rat_le_reflecting in F3.
  apply lt_le_trans with s';trivial.
  apply le_lt_trans with s;trivial.
  apply rat_le_reflecting.
  transitivity (abs (lim x - lim y));trivial.
  apply Rabs_nonneg.
}
pose (D := mkQpos Q d Hd).
pose (ED := mkQpos Q _ E4).
assert (Hrw : e = D + (ED / 4 + ED / 4) + (ED / 4 + ED / 4)).
{ path_via (D + ED).
  { apply (pos_eq Q);unfold D, ED.
    change (' e = d + (' e - d)).
    path_via ('e + (d - d));[|ring_tac.ring_with_nat].
    rewrite plus_negate_r,plus_0_r;trivial.
  }
  path_via (D + 4 / 4 * ED).
  { rewrite pos_recip_r,Qpos_mult_1_l;trivial. }
  apply (pos_eq Q);ring_tac.ring_with_nat.
}
rewrite Hrw.
eapply Requiv_triangle;[|apply equiv_lim].
apply IHy. apply (Rlt_close_rat_plus _ _ E2).
apply (non_expanding (fun u => abs (lim x - u))).
apply equiv_symm,equiv_lim.
Qed.

Lemma metric_to_equiv@{} : forall e u v, abs (u - v) < rat (' e) -> close e u v.
Proof.
intros e u v;revert u v e;apply (real_ind0 (fun u => forall v e, _ -> _));
[intros q|intros x IHx];
(apply (real_ind0 (fun v => forall e, _ -> _));[intros r|intros y IHy]);
intros e E1.
- apply equiv_rat_rat. apply Qclose_alt.
  apply rat_lt_reflecting,E1.
- apply metric_to_equiv_rat_lim;auto.
- apply equiv_symm,metric_to_equiv_rat_lim.
  + intros n n' E;apply equiv_symm,IHx.
    rewrite Rabs_neg_flip. trivial.
  + rewrite Rabs_neg_flip. trivial.
- apply metric_to_equiv_lim_lim;auto.
Qed.

Lemma equiv_metric_applied_rw'
  : forall e u v, close e u v = (abs (u - v) < rat (' e)).
Proof.
intros. apply TruncType.path_iff_ishprop_uncurried.
split.
- apply equiv_to_metric.
- apply metric_to_equiv.
Qed.

Definition equiv_metric_applied_rw@{} := equiv_metric_applied_rw'@{Ularge}.

Lemma equiv_metric_rw' : close = fun e u v => abs (u - v) < rat (' e).
Proof.
repeat (apply path_forall;intro).
apply equiv_metric_applied_rw.
Qed.

Definition equiv_metric_rw@{} := equiv_metric_rw'@{Ularge Ularge Ularge}.

Instance R_interval_restrict_nonexpanding@{}
  : forall (a b : real Q) E, NonExpanding (Interval_restrict a b E).
Proof.
intros a b E.
change (NonExpanding (fun z => join a (meet z b))).
apply _.
Qed.

Instance Q_interval_restrict_nonexpanding@{}
  : forall (a b : Q) E, NonExpanding (Interval_restrict a b E).
Proof.
intros a b E.
change (NonExpanding (fun z => join a (meet z b))).
apply _.
Qed.

Definition lipschitz_extend_interval@{} (a b : Q) (E : a <= b)
  (f : Interval a b -> real Q) (L:Q+)
  `{!Lipschitz f L}
  : Interval (rat a) (rat b) -> real Q
  := fun s => lipschitz_extend (compose f (Interval_restrict a b E)) L s.1.

Instance lipschitz_extend_interval_nonexpanding@{} (a b : Q) (E : a <= b)
  (f : Interval a b -> real Q)
  `{!NonExpanding f}
  : NonExpanding (lipschitz_extend_interval a b E f 1)
  := lipschitz_nonexpanding _.

Instance Rplus_le_preserving@{} : forall z : real Q,
  OrderPreserving (z +).
Proof.
intros z. hnf. unfold le;simpl. intros x y E.
rewrite <-E;clear E.
revert z x y;apply @unique_continuous_ternary_extension;try apply _.
{ intros x z;eapply @lipschitz_continuous;try apply _.
  apply (lipschitz_dup (fun y1 y2 => (x + y1) ⊔ (x + (y2 ⊔ z))));intros y;
  apply nonexpanding_lipschitz.
  { change (NonExpanding (compose ((x + y) ⊔) (compose (x +) (⊔ z)))).
    apply _. }
  { change (NonExpanding (compose (⊔ (x + (y ⊔ z))) (x +))).
    apply _. }
}
{ intros;eapply @lipschitz_continuous;try apply _.
  apply (lipschitz_dup (fun x1 x2 => (x1 + y) ⊔ (x2 + (y ⊔ z))));intros x;
  apply nonexpanding_lipschitz.
  { apply _. }
  { change (NonExpanding (compose (⊔ (x + (y ⊔ z))) (+ y))).
    apply _. }
}
intros;apply (ap rat).
apply join_r. apply (order_preserving (q +)).
apply join_ub_l.
Qed.

Lemma Rlt_close_plus@{} : forall u v, u < v ->
  forall w e, close e u w -> w < v + rat (' e).
Proof.
intros u v E w e xi;revert E;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
apply R_lt_le_trans with (rat (r + ' e)).
- apply Rlt_close_rat_plus with u;trivial.
  apply R_le_lt_trans with (rat q);trivial.
  apply rat_lt_preserving;trivial.
- rewrite plus_comm. rewrite Rplus_comm.
  change (rat (' e) + rat r <= rat (' e) + v).
  apply (order_preserving (rat (' e) +)). trivial.
Qed.

Lemma Rplus_le_reflecting@{} : forall z : real Q,
  OrderReflecting (z +).
Proof.
intros z;hnf;unfold le;simpl;intros x y E.
assert (Hrw : y = z + y - z).
{ rewrite (commutativity (f:=plus) z y),
  <-(simple_associativity (f:=plus) y z (-z)).
  rewrite right_inverse,right_identity. trivial.
}
path_via (z + y - z);clear Hrw.
rewrite <-E. clear E.
revert z x y;apply @unique_continuous_ternary_extension;try apply _.
{ change (forall x y, Continuous (compose (+ (- x)) (compose ((x + y) ⊔) (x +)))).
  apply _. }
{ change (forall x z, Continuous (compose (+ (- x)) (compose (⊔ (x + z)) (x +)))).
  apply _. }
{ intros y z;eapply @lipschitz_continuous;try apply _.
  apply (lipschitz_dup (fun x1 x2 => (x1 + y) ⊔ (x1 + z) - x2)).
  { apply _. }
  { intros x0;apply (@lipschitz_dup (fun x1 x2 => (x1 + y) ⊔ (x2 + z) - x0) 1 1).
    { change (forall x,
      Lipschitz (compose (+ (- x0)) (compose ((x + y) ⊔) (+ z))) (1:Q+)).
      apply _. }
    { change (forall y0,
      Lipschitz (compose (+ (- x0)) (compose (⊔ (y0 + z)) (+ y))) (1:Q+)).
      apply _. }
  }
}
intros;apply (ap rat).
destruct (total le r s) as [E|E].
- rewrite (join_r _ _ E).
  rewrite (join_r _ _ (order_preserving (q +) _ _ E)).
  rewrite (plus_comm q s),<-plus_assoc,plus_negate_r,plus_0_r;trivial.
- rewrite (join_l _ _ E).
  rewrite (join_l _ _ (order_preserving (q +) _ _ E)).
  rewrite (plus_comm q r),<-plus_assoc,plus_negate_r,plus_0_r;trivial.
Unshelve. exact 1.
Qed.

Instance Rplus_le_embedding@{} : forall z : real Q, OrderEmbedding (z +).
Proof.
intros;split.
- apply Rplus_le_preserving.
- apply Rplus_le_reflecting.
Qed.

Lemma Rneg_le_flip@{} : forall x y : real Q, x <= y -> - y <= - x.
Proof.
intros x y E.
rewrite <-E.
clear E;revert x y;apply @unique_continuous_binary_extension.
{ change (forall x, Continuous (compose (⊔ - x) (compose (-) (x ⊔))));apply _. }
{ intros;eapply @lipschitz_continuous;try apply _.
  apply (lipschitz_dup (fun x1 x2 => - (x1 ⊔ y) ⊔ - x2));intros x;
  apply nonexpanding_lipschitz.
  { change (NonExpanding (compose (- (x ⊔ y) ⊔) (-)));apply _. }
  { change (NonExpanding (compose (⊔ - x) (compose (-) (⊔ y))));apply _. }
}
{ apply _. }
{ apply _. }
intros q r;apply (ap rat).
apply join_r. apply (snd (flip_le_negate _ _)). apply join_ub_l.
Unshelve. exact 1.
Qed.

Lemma Rneg_le_flip_equiv@{} : forall x y : real Q, - y <= - x <-> x <= y.
Proof.
intros x y;split.
- intros E. apply Rneg_le_flip in E. rewrite !involutive in E.
  exact E.
- apply Rneg_le_flip.
Qed.

Lemma Rneg_lt_flip@{} : forall x y : real Q, - y < - x <-> x < y.
Proof.
intros x y;split;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
- apply flip_lt_negate in E2.
  apply Rneg_le_flip in E1;apply Rneg_le_flip in E3.
  rewrite involutive in E1;rewrite involutive in E3.
  apply tr;exists (-r),(-q). auto.
- apply tr;exists (-r),(-q);repeat split.
  + change (- y <= - (rat r)). apply (snd (Rneg_le_flip_equiv _ _)),E3.
  + apply (snd (flip_lt_negate _ _)),E2.
  + change (- rat q <= - x). apply (snd (Rneg_le_flip_equiv _ _)),E1.
Qed.

Definition Qpos_diff : forall q r : Q, q < r -> Q+.
Proof.
intros q r E;exists (r-q).
apply (snd (flip_pos_minus _ _) E).
Defined.

Lemma Qpos_diff_pr@{} : forall q r E, r = q + ' (Qpos_diff q r E).
Proof.
intros q r E. change (r = q + (r - q)).
path_via (r + (q - q));[|ring_tac.ring_with_nat].
rewrite plus_negate_r,plus_0_r;trivial.
Qed.

Lemma Rlt_cotrans_rat@{} : forall x q r, q < r -> hor (rat q < x) (x < rat r).
Proof.
apply (real_ind0 (fun x => forall q r, _ -> _)).
- intros s q r E. generalize (cotransitive E s).
  apply (Trunc_ind _);intros [E'|E'];apply tr;[left|right];
  apply rat_lt_preserving,E'.
- intros x IH q r E0.
  destruct (Q_dense _ _ E0) as [q1 [E1 E2]].
  destruct (Q_dense _ _ E2) as [r1 [E3 E4]].
  clear E0 E2.
  destruct (Qpos_lt_min (Qpos_diff _ _ E1) (Qpos_diff _ _ E4))
    as [n [n1 [n2 [Hn1 Hn2]]]].
  generalize (IH n _ _ E3);apply (Trunc_ind _).
  intros [E5|E5];apply tr;[left|right].
  + apply Rneg_lt_flip. change (- lim x < rat (- q)).
    assert (Hrw : - q = - q1 + ' Qpos_diff q q1 E1).
    { set (D := Qpos_diff q q1 E1).
      rewrite (Qpos_diff_pr _ _ E1). unfold D;clear D.
      rewrite negate_plus_distr. rewrite <-plus_assoc,plus_negate_l,plus_0_r.
      trivial.
    }
    rewrite Hrw;clear Hrw.
    apply Rlt_close_rat_plus with (- (x n)).
    * apply (snd (Rneg_lt_flip _ _) E5).
    * apply (non_expanding (-)).
      rewrite Hn1. rewrite qpos_plus_comm. apply equiv_lim.
  + rewrite (Qpos_diff_pr _ _ E4).
    apply Rlt_close_rat_plus with (x n);trivial.
    rewrite Hn2,qpos_plus_comm. apply equiv_lim.
Qed.

Instance Rlt_cotrans@{} : CoTransitive (@lt (real Q) _).
Proof.
hnf. intros x y E z;revert E;apply (Trunc_ind _);intros [q [r [E1 [E2 E3]]]].
generalize (Rlt_cotrans_rat z q r E2);apply (Trunc_ind _).
intros [E4|E4];apply tr;[left|right].
- apply R_le_lt_trans with (rat q);trivial.
- apply R_lt_le_trans with (rat r);trivial.
Qed.

Instance Rap_cotrans@{} : CoTransitive (@apart (real Q) _).
Proof.
hnf. intros x y [E|E] z.
- apply (merely_destruct (cotransitive E z)).
  intros [E1|E1];apply tr;[left|right];hnf;auto.
- apply (merely_destruct (cotransitive E z)).
  intros [E1|E1];apply tr;[right|left];hnf;auto.
Qed.

Lemma Qabs_le_raw@{} : forall x : Q, x <= abs x.
Proof.
intros x;destruct (total_abs_either x) as [[E1 E2]|[E1 E2]].
- rewrite E2;reflexivity.
- transitivity (0:Q);trivial.
  rewrite E2. apply flip_nonpos_negate. trivial.
Qed.

Lemma Qabs_neg@{} : forall x : Q, abs (- x) = abs x.
Proof.
intros x. destruct (total_abs_either x) as [[E1 E2]|[E1 E2]].
- rewrite E2. path_via (- - x);[|rewrite involutive;trivial].
  apply ((abs_sig (- x)).2). apply flip_nonneg_negate;trivial.
- rewrite E2. apply ((abs_sig (- x)).2). apply flip_nonpos_negate;trivial.
Qed.

Lemma Qabs_le_neg_raw : forall x : Q, - x <= abs x.
Proof.
intros x. rewrite <-Qabs_neg. apply Qabs_le_raw.
Qed.

Lemma Q_abs_le_pr@{} : forall x y : Q, abs x <= y <-> - y <= x /\ x <= y.
Proof.
intros x y;split.
- intros E. split.
  + apply flip_le_negate. rewrite involutive. transitivity (abs x);trivial.
    apply Qabs_le_neg_raw.
  + transitivity (abs x);trivial.
    apply Qabs_le_raw.
- intros [E1 E2].
  destruct (total_abs_either x) as [[E3 E4]|[E3 E4]];rewrite E4.
  + trivial.
  + apply flip_le_negate;rewrite involutive;trivial.
Qed.

Lemma Qabs_is_join@{} : forall q : Q, abs q = join (- q) q.
Proof.
intros q. symmetry.
destruct (total_abs_either q) as [[E1 E2]|[E1 E2]];rewrite E2.
- apply join_r. transitivity (0:Q);trivial.
  apply flip_nonneg_negate;trivial.
- apply join_l. transitivity (0:Q);trivial.
  apply flip_nonpos_negate;trivial.
Qed.

Lemma Rabs_is_join@{} : forall x : real Q, abs x = join (- x) x.
Proof.
eapply @unique_continuous_extension;try apply _.
{ eapply @lipschitz_continuous;try apply _.
  apply (lipschitz_dup (fun u1 u2 => join (- u1) u2));
  intros;apply nonexpanding_lipschitz.
  { apply _. }
  { change (NonExpanding (compose (⊔ y) (-)));apply _. }
}
intros;apply (ap rat),Qabs_is_join.
Qed.

Lemma Rabs_le_raw@{} : forall x : real Q, x <= abs x.
Proof.
intros x;rewrite Rabs_is_join. apply join_ub_r.
Qed.

Lemma Rabs_le_neg_raw@{} : forall x : real Q, - x <= abs x.
Proof.
intros x;rewrite Rabs_is_join. apply join_ub_l.
Qed.

Lemma Rabs_neg@{} : forall x : real Q, abs (- x) = abs x.
Proof.
intros;rewrite !Rabs_is_join,involutive. apply commutativity.
Qed.

Lemma Rabs_le_pr@{} : forall x y : real Q, abs x <= y <-> - y <= x /\ x <= y.
Proof.
intros x y.
split.
- intros E. split.
  + apply Rneg_le_flip_equiv. rewrite involutive. transitivity (abs x);trivial.
    apply Rabs_le_neg_raw.
  + transitivity (abs x);trivial.
    apply Rabs_le_raw.
- intros [E1 E2].
  rewrite Rabs_is_join. apply join_le.
  + apply Rneg_le_flip_equiv;rewrite involutive;trivial.
  + trivial.
Qed.

Lemma abs_plus_1_lt@{} : forall q : Q, abs q < abs q + 1.
Proof.
intros. apply pos_plus_lt_compat_r. solve_propholds.
Qed.

Lemma abs_plus_1_pos@{} : forall q : Q, 0 < abs q + 1.
Proof.
intros. apply le_lt_trans with (abs q).
- apply Qabs_nonneg.
- apply abs_plus_1_lt.
Qed.

Lemma R_Qpos_bounded@{} : forall x : real Q,
  merely (exists q : Q+, abs x <= rat (' q)).
Proof.
apply (real_ind0 _).
- intros q;apply tr. simple refine (existT _ _ _).
  + exists (abs q + 1). apply abs_plus_1_pos.
  + simpl. apply rat_le_preserve. change (abs q <= abs q + 1).
    apply lt_le. apply abs_plus_1_lt.
- intros x IH.
  generalize (IH 1).
  apply (Trunc_ind _);intros [q E].
  apply tr;exists (q + 2).
  eapply Rle_close_rat;[apply E|].
  apply (non_expanding abs).
  apply equiv_lim.
Defined.

Definition Qbounded_square (a : Q) : Interval (- a) a -> Q :=
  fun x => x.1 * x.1.

Lemma Qabs_mult@{} : forall a b : Q, abs (a * b) = abs a * abs b.
Proof.
intros a b.
destruct (total_abs_either a) as [Ea|Ea];destruct Ea as [Ea1 Ea2];rewrite Ea2;
destruct (total_abs_either b) as [Eb|Eb];destruct Eb as [Eb1 Eb2];rewrite Eb2.
- apply ((abs_sig (a*b)).2). apply nonneg_mult_compat;trivial.
- rewrite <-negate_mult_distr_r.
  apply ((abs_sig (a*b)).2). apply nonneg_nonpos_mult;trivial.
- rewrite <-negate_mult_distr_l.
  apply ((abs_sig (a*b)).2). apply nonpos_nonneg_mult;trivial.
- rewrite negate_mult_negate. apply ((abs_sig (a*b)).2).
  apply nonpos_mult;trivial.
Qed.

Lemma Qbounded_square_lipschitz@{}
  : forall a : Q+, Lipschitz (Qbounded_square (' a)) (2 * a).
Proof.
intros a e [q Hq] [r Hr] xi.
change (close e q r) in xi.
unfold Qbounded_square;simpl.
apply Qclose_alt in xi. apply Qclose_alt.
assert (Hrw : q * q - r * r = (q + r) * (q - r)).
{ path_via (q * q + - r * r + (q * r + q * - r));[|ring_tac.ring_with_nat].
  rewrite negate_mult_distr_l,<-negate_mult_distr_r,plus_negate_r,plus_0_r.
  trivial. }
rewrite Hrw. clear Hrw.
rewrite Qabs_mult. change (' (2 * a * e)) with (2 * ' a * ' e).
apply pos_mult_le_lt_compat;[split| |split].
- apply Qabs_nonneg.
- assert (Hrw : 2 * ' a = ' a + ' a) by ring_tac.ring_with_nat.
  rewrite Hrw;clear Hrw.
  rewrite Qabs_is_join. destruct Hq,Hr. apply join_le.
  + rewrite negate_plus_distr.
    apply plus_le_compat;apply flip_le_negate;rewrite involutive;trivial.
  + apply plus_le_compat;trivial.
- change (0 < ' (2 * a)). solve_propholds.
- apply Qabs_nonneg.
- trivial.
Qed.
Existing Instance Qbounded_square_lipschitz.

Lemma Qpos_neg_le@{} : forall a : Q+, - ' a <= ' a.
Proof.
intros a;transitivity (0:Q).
- apply flip_nonneg_negate. solve_propholds.
- solve_propholds.
Qed.

Definition Rbounded_square@{} (a : Q+)
  : Interval (- rat (' a)) (rat (' a)) -> real Q.
Proof.
exact (lipschitz_extend_interval (- ' a) (' a) (Qpos_neg_le _)
  (compose rat (Qbounded_square (' a))) _).
Defined.

Instance Rbounded_square_lipschitz@{}
  : forall a : Q+, Lipschitz (Rbounded_square a) (2*a).
Proof.
intros a.
pose proof (_ : Lipschitz (Rbounded_square a) (_:Q+)) as E.
rewrite Qpos_mult_1_l,qpos_mult_comm,Qpos_mult_1_l in E. exact E.
Qed.

Definition Rfull_square (s : sigT (fun a => Interval (- (rat (' a))) (rat (' a))))
  := Rbounded_square s.1 s.2.

Definition interval_back
  : sigT (fun a : Q+ => Interval (- rat (' a)) (rat (' a))) -> real Q
  := fun x => x.2.1.

Instance interval_proj_issurj@{}
  : TrM.IsConnMap@{Uhuge Ularge UQ UQ Ularge} (trunc_S minus_two) interval_back.
Proof.
apply BuildIsSurjection. intros x.
generalize (R_Qpos_bounded x). apply (Trunc_ind _);intros [q E].
apply tr. simple refine (existT _ _ _).
- exists q. exists x. apply Rabs_le_pr. exact E.
- simpl. reflexivity.
Defined.

Definition Rinterval_inject@{} : forall a b : Q, a <= b ->
  Interval (- rat a) (rat a) -> Interval (- (rat b)) (rat b).
Proof.
intros a b E s.
exists (s.1).
split.
- transitivity (- (rat a));[|apply s.2].
  apply Rneg_le_flip,rat_le_preserve,E.
- transitivity (rat a);[apply s.2|].
  apply rat_le_preserve,E.
Defined.

Lemma Rbounded_square_respects : ∀ x y, interval_back x = interval_back y →
  Rbounded_square x.1 x.2 = Rbounded_square y.1 y.2.
Proof. Admitted.

Definition Rsquare@{} : real Q -> real Q
  := jections.surjective_factor@{UQ UQ UQ Uhuge Ularge
    Ularge UQ UQ Uhuge Ularge
    UQ} Rfull_square interval_back Rbounded_square_respects.

Lemma Rsquare_pr@{} : Rfull_square = compose Rsquare interval_back.
Proof.
apply jections.surjective_factor_pr.
Qed.

Definition pos_of_Q : Q -> Q+
  := fun q => {| pos := abs q + 1; is_pos := abs_plus_1_pos q |}.

Lemma Q_abs_plus_1_bounds@{} : forall q : Q,
  - ' (pos_of_Q q) ≤ q
  ≤ ' (pos_of_Q q).
Proof.
intros. change (- (abs q + 1) ≤ q ≤ (abs q + 1)). split.
- apply flip_le_negate. rewrite involutive.
  transitivity (abs q).
  + apply Qabs_le_neg_raw.
  + apply nonneg_plus_le_compat_r. solve_propholds.
- transitivity (abs q).
  + apply Qabs_le_raw.
  + apply nonneg_plus_le_compat_r. solve_propholds.
Qed.

Lemma Rsquare_rat@{} q : Rsquare (rat q) = rat (q * q).
Proof.
unfold Rsquare,jections.surjective_factor,jections.surjective_factor_aux.
simpl. unfold Rfull_square,Rbounded_square. simpl.
unfold lipschitz_extend_interval. simpl.
unfold compose. rewrite lipschitz_extend_rat.
rewrite (Interval_restrict_pr _ _ _ _ (Q_abs_plus_1_bounds q)). reflexivity.
Qed.

Instance Qmult_lipschitz@{} : forall q : Q, Lipschitz (q *.) (pos_of_Q q).
Proof.
intros q e x y xi.
apply Qclose_alt.
rewrite negate_mult_distr_r,<-plus_mult_distr_l,Qabs_mult.
apply pos_mult_le_lt_compat;try split.
- apply Qabs_nonneg.
- rewrite Qabs_is_join. apply join_le.
  + apply flip_le_negate;rewrite involutive; apply Q_abs_plus_1_bounds.
  + apply Q_abs_plus_1_bounds.
- solve_propholds.
- apply Qabs_nonneg.
- apply Qclose_alt,xi.
Qed.

Definition QRmult@{} : Q -> real Q -> real Q
  := fun q => lipschitz_extend (compose rat (q *.)) (pos_of_Q q).

Global Instance Rmult@{} : Mult (real Q)
  := fun u v => QRmult (/ 2) (Rsquare (u + v) - Rsquare u - Rsquare v).

Lemma Rmult_rat_rat@{} : forall q r, rat q * rat r = rat (q * r).
Proof.
intros. unfold mult at 1. unfold Rmult,QRmult.
change (rat q + rat r) with (rat (q + r)).
rewrite !Rsquare_rat.
change (rat ((q + r) * (q + r)) - rat (q * q) - rat (r * r)) with
  (rat ((q + r) * (q + r) - q * q - r * r)).
rewrite lipschitz_extend_rat. unfold compose. apply ap.
path_via ((2 * q * r + (q * q - q * q) + (r * r - r * r)) / 2).
{ ring_tac.ring_with_nat. }
rewrite !plus_negate_r,!plus_0_r.
path_via (2 / 2 * q * r).
{ ring_tac.ring_with_nat. }
rewrite dec_recip_inverse;[|solve_propholds].
rewrite mult_1_l;trivial.
Qed.

End contents.
