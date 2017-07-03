Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.FunextAxiom
  HoTT.UnivalenceAxiom
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.integers
  HoTTClasses.interfaces.naturals
  HoTTClasses.interfaces.rationals
  HoTTClasses.interfaces.orders
  HoTTClasses.implementations.natpair_integers
  HoTTClasses.theory.rings
  HoTTClasses.theory.integers
  HoTTClasses.theory.dec_fields
  HoTTClasses.orders.dec_fields
  HoTTClasses.theory.rationals
  HoTTClasses.orders.lattices
  HoTTClasses.theory.additional_operations
  HoTTClasses.theory.premetric.

Local Set Universe Minimization ToSet.

Module Export Cauchy.

Section DefSec.
Variable T : Type@{UQ}.
Context {Tclose : Closeness T}.

Private Inductive C@{} : Type@{UQ} :=
  | eta : T -> C
  | Clim : Lim C

with equiv@{} : Closeness@{UQ} C :=
  (* TODO NonExpanding eta ?? *)
  | equiv_eta_eta : forall (q r : T) (e : Q+),
      close e q r ->
      close e (eta q) (eta r)
  | equiv_eta_lim' : forall q (y : Approximation C) (e d d' : Q+),
      e = d + d' ->
      close d' (eta q) (y d) ->
      close e (eta q) (Clim y)
  | equiv_lim'_eta : forall (x : Approximation C) r (e d d' : Q+),
      e = d + d' ->
      close d' (x d) (eta r) ->
      close e (Clim x) (eta r)
  | equiv_lim'_lim' : forall (x y : Approximation C) (e d n e' : Q+),
      e = d + n + e' ->
      close e' (x d) (y n) ->
      close e (Clim x) (Clim y)
.

Global Existing Instance equiv | 5.

Axiom equiv_path@{} : Separated C.
Axiom equiv_hprop@{} : forall e (u v : C), IsHProp (close e u v).
Global Existing Instance equiv_path.
Global Existing Instance equiv_hprop.

Global Existing Instance Clim.

Definition equiv_eta_lim@{} : forall q (y:Approximation C) (e d d' : Q+),
  e = d + d' ->
  close d' (eta q) (y d) ->
  close e (eta q) (lim y)
  := equiv_eta_lim'.

Definition equiv_lim_eta@{} : forall (x:Approximation C) r (e d d' : Q+),
  e = d + d' ->
  close d' (x d) (eta r) ->
  close e (lim x) (eta r)
  := equiv_lim'_eta.

Definition equiv_lim_lim@{} : forall (x y : Approximation C) (e d n e' : Q+),
  e = d + n + e' ->
  close e' (x d) (y n) ->
  close e (lim x) (lim y)
  := equiv_lim'_lim'.

Record DApproximation@{UA UB} (A : C -> Type@{UA})
  (B : forall x y : C, A x -> A y -> forall e, close e x y -> Type@{UB})
  (x : Approximation C) :=
  { dapproximation :> forall e, A (x e)
  ; dapproximation_correct :
    forall d e, B (x d) (x e) (dapproximation d) (dapproximation e) (d+e)
      (approx_equiv _ _ _) }.

Record Inductors@{UA UB} (A : C -> Type@{UA})
  (B : forall x y : C, A x -> A y -> forall e, close e x y -> Type@{UB}) :=
  { ind_eta : forall q, A (eta q)
  ; ind_lim : forall (x:Approximation C) (a : DApproximation A B x),
    A (lim x)

  ; ind_path_A : forall u v (u_equiv_v : forall e, close e u v),
    forall (a : A u) (b : A v), (forall e, B u v a b e (u_equiv_v _)) ->
    equiv_path u v u_equiv_v # a = b

  ; ind_eta_eta : forall q r e (Hqr : close e q r),
      @B (eta q) (eta r) (ind_eta q) (ind_eta r) e (equiv_eta_eta _ _ _ Hqr)
  ; ind_eta_lim : forall q d d' e y (b : DApproximation A B y)
      (He : e = d + d')
      (xi : close d' (eta q) (y d)),
      B (eta q) (y d) (ind_eta q) (b d) d' xi ->
      @B (eta q) (lim y) (ind_eta q) (ind_lim y b) e
         (equiv_eta_lim _ _ _ _ _ He xi)
   ; ind_lim_eta : forall r d d' e x (a : DApproximation A B x)
      (He : e = d + d')
      (xi : close d' (x d) (eta r)),
      B (x d) (eta r) (a d) (ind_eta r) d' xi ->
      @B (lim x) (eta r) (ind_lim x a) (ind_eta r) e
         (equiv_lim_eta _ _ _ _ _ He xi)
   ; ind_lim_lim : forall x y (a : DApproximation A B x) (b : DApproximation A B y)
      e d n e' (He : e = d + n + e')
      (xi : close e' (x d) (y n)),
      B (x d) (y n) (a d) (b n) e' xi ->
      @B (lim x) (lim y) (ind_lim x a) (ind_lim y b) e
         (equiv_lim_lim _ _ _ _ _ _ He xi)

   ; ind_hprop_B : forall x y a b e xi, IsHProp (@B x y a b e xi) }.

Arguments ind_eta {_ _} _ _.
Arguments ind_lim {_ _} _ _ _.
Arguments ind_eta_eta {_ _} _ _ _ _ _.
Arguments ind_eta_lim {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_eta {_ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_lim {_ _} _ _ _ _ _ _ _ _ _ _ _ _.

Section induction.
Universe UA UB.
Variable A : C -> Type@{UA}.
Variable B : forall x y : C, A x -> A y -> forall e, close e x y -> Type@{UB}.

Definition C_rect@{} : Inductors A B -> forall x : C, A x :=
  fix C_rect (I : Inductors A B) (x : C) {struct x} : A x :=
    match x return (Inductors A B -> A x) with
    | eta q => fun I => ind_eta I q
    | Clim x => fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      ind_lim I x a
    end I

  with equiv_rect (I : Inductors A B) (x y : C) (e : Q+) (xi : close e x y)
    {struct xi} : B x y (C_rect I x) (C_rect I y) e xi :=
    match xi in equiv e' x' y' return
      (forall I : Inductors A B,
        @B x' y' (C_rect I x') (C_rect I y') e' xi) with
    | equiv_eta_eta q r e H => fun I => ind_eta_eta I q r e H
    | equiv_eta_lim' q y e d d' He xi =>
      fun I =>
      let b := Build_DApproximation A B y (fun e => C_rect I (y e))
        (fun d e => equiv_rect I (y d) (y e) _ (approx_equiv y d e)) in
      ind_eta_lim I q d d' e y b He xi (equiv_rect I _ _ _ xi)
    | equiv_lim'_eta x r e d d' He xi =>
      fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      ind_lim_eta I r d d' e x a He xi (equiv_rect I _ _ _ xi)
    | equiv_lim'_lim' x y e d n e' He xi =>
      fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      let b := Build_DApproximation A B y (fun e => C_rect I (y e))
        (fun d e => equiv_rect I (y d) (y e) _ (approx_equiv y d e)) in
      ind_lim_lim I x y a b e d n e' He xi (equiv_rect I _ _ _ xi)
    end I
  for C_rect.

Definition equiv_rect@{} : forall (I : Inductors A B)
  {x y : C} {e : Q+} (xi : close e x y),
  B x y (C_rect I x) (C_rect I y) e xi :=
  fix C_rect (I : Inductors A B) (x : C) {struct x} : A x :=
    match x return (Inductors A B -> A x) with
    | eta q => fun I => ind_eta I q
    | Clim x => fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      ind_lim I x a
    end I

  with equiv_rect (I : Inductors A B) (x y : C) (e : Q+) (xi : close e x y)
    {struct xi} : B x y (C_rect I x) (C_rect I y) e xi :=
    match xi in equiv e' x' y' return
      (forall I : Inductors A B,
        @B x' y' (C_rect I x') (C_rect I y') e' xi) with
    | equiv_eta_eta q r e H => fun I => ind_eta_eta I q r e H
    | equiv_eta_lim' q y e d d' He xi =>
      fun I =>
      let b := Build_DApproximation A B y (fun e => C_rect I (y e))
        (fun d e => equiv_rect I (y d) (y e) _ (approx_equiv y d e)) in
      ind_eta_lim I q d d' e y b He xi (equiv_rect I _ _ _ xi)
    | equiv_lim'_eta x r e d d' He xi =>
      fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      ind_lim_eta I r d d' e x a He xi (equiv_rect I _ _ _ xi)
    | equiv_lim'_lim' x y e d n e' He xi =>
      fun I =>
      let a := Build_DApproximation A B x (fun e => C_rect I (x e))
        (fun d e => equiv_rect I (x d) (x e) _ (approx_equiv x d e)) in
      let b := Build_DApproximation A B y (fun e => C_rect I (y e))
        (fun d e => equiv_rect I (y d) (y e) _ (approx_equiv y d e)) in
      ind_lim_lim I x y a b e d n e' He xi (equiv_rect I _ _ _ xi)
    end I
  for equiv_rect.

Definition approx_rect@{} (I : Inductors A B) (x : Approximation C)
  : DApproximation A B x
  := Build_DApproximation A B x (fun e => C_rect I (x e))
      (fun d e => equiv_rect I (approx_equiv x d e)).

Variable I : Inductors A B.

Definition C_rect_eta@{} q : C_rect I (eta q) = ind_eta I q
  := idpath.

Definition C_rect_lim@{} x : C_rect I (lim x) = ind_lim I x (approx_rect I x)
  := idpath.

Definition equiv_rect_eta_eta@{} q r e E : equiv_rect I (equiv_eta_eta q r e E)
  = ind_eta_eta I q r e E
  := idpath.

Definition equiv_rect_eta_lim@{} q y e d d' He xi
  : equiv_rect I (equiv_eta_lim q y e d d' He xi)
  = ind_eta_lim I q d d' e y (approx_rect I y) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_rat@{} x r e d d' He xi
  : equiv_rect I (equiv_lim_eta x r e d d' He xi)
  = ind_lim_eta I r d d' e x (approx_rect I x) He xi (equiv_rect I xi)
  := idpath.

Definition equiv_rect_lim_lim@{} x y e d n e' He xi
  : equiv_rect I (equiv_lim_lim x y e d n e' He xi)
  = ind_lim_lim I x y (approx_rect I x) (approx_rect I y)
                  e d n e' He xi (equiv_rect I xi)
  := idpath.

End induction.

End DefSec.

Arguments eta {_ _} _.
Arguments ind_eta {_ _ _ _} _ _.
Arguments ind_lim {_ _ _ _} _ _ _.
Arguments ind_eta_eta {_ _ _ _} _ _ _ _ _.
Arguments ind_eta_lim {_ _ _ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_eta {_ _ _ _} _ _ _ _ _ _ _ _ _ _.
Arguments ind_lim_lim {_ _ _ _} _ _ _ _ _ _ _ _ _ _ _ _.

(* These don't get refolded so simpl produces the huge fix expression. *)
Arguments C_rect T {Tclose} A B I x : simpl never.
Arguments equiv_rect T {Tclose} A B I {x y e} xi : simpl never.

End Cauchy.

Section generalities.
Variable T : Type@{UQ}.
Context {Tclose : Closeness T} {Tpremetric : PreMetric T}.

Definition C_rect0@{UA} (A : C T -> Type@{UA})
  (val_eta : forall q, A (eta q))
  (val_lim : forall (x : Approximation (C T)) (a : forall e, A (x e)), A (lim x))
  (val_respects : forall u v (h : forall e, close e u v) (a : A u) (b : A v),
    equiv_path T u v h # a = b)
  : forall x, A x.
Proof.
apply (C_rect T A (fun _ _ _ _ _ _ => Unit)).
split;auto.
- intros. apply val_lim. intros;apply a.
- intros _ _ _ _ _ _. apply trunc_succ.
  (* ^ must be done by hand
       otherwise it uses some instance that needs a universe > Set *)
Defined.

Definition C_ind0@{UA} (A : C T -> Type@{UA})
  `{forall q, IsHProp (A q)}
  (A_eta : forall q, A (eta q))
  (A_lim : forall (x : Approximation (C T)) (a : forall e, A (x e)), A (lim x))
  : forall x, A x.
Proof.
apply C_rect0;auto.
intros. apply path_ishprop.
Defined.

Lemma equiv_refl@{} : forall e, Reflexive (close (A:=C T) e).
Proof.
red. intros e u;revert u e.
apply (C_ind0 (fun u => forall e, _)).
- intros. apply equiv_eta_eta. reflexivity.
- intros. eapply equiv_lim_lim;[apply pos_split3|].
  trivial.
Qed.

Existing Instance equiv_refl.

Lemma C_isset@{} : IsHSet (C T).
Proof.
eapply @HSet.isset_hrel_subpaths.
3:apply equiv_path.
- red. intros;reflexivity.
- apply _.
Qed.

Global Existing Instance C_isset.

Definition const_approx@{} : C T -> Approximation (C T).
Proof.
intros x;exists (fun _ => x).
intros;reflexivity.
Defined.

Lemma lim_cons@{} : forall x, lim (const_approx x) = x.
Proof.
apply (C_ind0 _).
- intros. apply equiv_path.
  intros. eapply equiv_lim_eta;[apply pos_split2|].
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

Definition lim_issurj : IsSurjection (lim (A:=C T)).
Proof.
apply BuildIsSurjection.
intros. apply tr. exists (const_approx b).
apply lim_cons.
Defined.

Lemma lim_epi@{i j k} : epi.isepi@{UQ UQ i j k} (lim (A:=C T)).
Proof.
apply epi.issurj_isepi@{UQ UQ Uhuge Ularge i
  k Ularge j}.
exact lim_issurj.
Qed.

Definition equiv_rect0@{i}
  (P : forall e (u v : C T), close e u v -> Type@{i})
  `{forall e u v xi, IsHProp (P e u v xi)}
  (val_eta_eta : forall q r e He, P _ _ _ (equiv_eta_eta _ q r e He))
  (val_eta_lim : forall q (y : Approximation (C T)) e d d' He xi,
    P d' (eta q) (y d) xi ->
    P e (eta q) (lim y) (equiv_eta_lim _ q y e d d' He xi))
  (val_lim_eta : forall (x : Approximation (C T)) r e d d' He xi,
    P d' (x d) (eta r) xi ->
    P e (lim x) (eta r) (equiv_lim_eta _ x r e d d' He xi))
  (val_lim_lim : forall (x y : Approximation (C T)) e d n e' He xi,
    P e' (x d) (y n) xi ->
    P e (lim x) (lim y) (equiv_lim_lim _ x y e d n e' He xi))
  : forall e u v xi, P e u v xi.
Proof.
intros e u v;revert u v e.
apply (equiv_rect _ (fun _ => Unit) (fun x y _ _ e xi => P e x y xi)).
split;auto.
intros. apply @path_ishprop,trunc_succ.
Defined.

Definition equiv_rec0@{i} (P : Q+ -> C T -> C T -> Type@{i})
  `{forall e u v, IsHProp (P e u v)}
  := equiv_rect0 (fun e u v _ => P e u v).

Instance equiv_symm@{} : forall e, Symmetric (close (A:=C T) e).
Proof.
red. apply (equiv_rec0 _).
- intros q r e He. apply equiv_eta_eta. symmetry;trivial.
- intros q y e d d' He _ xi.
  apply equiv_lim_eta with d d';trivial.
- intros x r e d d' He _ xi.
  apply equiv_eta_lim with d d';trivial.
- intros x y e d n e' He _ xi.
  apply equiv_lim_lim with n d e';trivial.
  rewrite (commutativity (f:=plus) n d).
  trivial.
Qed.

Lemma equiv_symm_rw@{i} : forall e (u v : C  T),
  paths@{i} (close e u v) (close e v u).
Proof.
intros. apply path_universe_uncurried.
apply equiv_iff_hprop_uncurried.
split;apply equiv_symm.
Qed.

Section mutual_recursion.
Universe UA UB.
Variables (A : Type@{UA}) (B : Q+ -> A -> A -> Type@{UB}).

Record Recursors@{} :=
  { rec_eta : T -> A
  ; rec_lim : Approximation (C T) ->
      forall val_ind : Q+ -> A,
      (forall d e, B (d + e) (val_ind d) (val_ind e)) -> A
  ; rec_separated : forall x y, (forall e, B e x y) -> x = y
  ; rec_hprop : forall e x y, IsHProp (B e x y)
  ; rec_eta_eta : forall q r e, close e q r -> B e (rec_eta q) (rec_eta r)
  ; rec_eta_lim : forall q d d' e (y : Approximation (C T)) (b : Q+ -> A)
      (Eb : forall d e, B (d + e) (b d) (b e)),
      e = d + d' -> close d' (eta q) (y d) ->
      B d' (rec_eta q) (b d) ->
      B e (rec_eta q) (rec_lim y b Eb)
  ; rec_lim_eta : forall r d d' e (x : Approximation (C T)) (a : Q+ -> A)
      (Ea : forall d e, B (d+e) (a d) (a e)),
      e = d + d' ->
      close d' (x d) (eta r) ->
      B d' (a d) (rec_eta r) ->
      B e (rec_lim x a Ea) (rec_eta r)
  ; rec_lim_lim : forall (x y : Approximation (C T)) (a b : Q+ -> A)
      (Ea : forall d e, B (d + e) (a d) (a e))
      (Eb : forall d e, B (d + e) (b d) (b e))
      e d n e',
      e = d + n + e' ->
      close e' (x d) (y n) ->
      B e' (a d) (b n) ->
      B e (rec_lim x a Ea) (rec_lim y b Eb) }.

Definition recursors_inductors@{}
  : Recursors ->
  Inductors T (fun _ => A) (fun _ _ x y e _ => B e x y).
Proof.
intros I.
simple refine (Build_Inductors _ _ _ _ _ _ _ _ _ _ _).
- exact (rec_eta I).
- intros x [a Ea];revert x a Ea;simpl;exact (rec_lim I).
- intros;rewrite PathGroupoids.transport_const;apply (rec_separated I);trivial.
- exact (rec_eta_eta I).
- intros ????? [b Eb];simpl. apply rec_eta_lim.
- intros ????? [a Ea];simpl. apply rec_lim_eta.
- intros ?? [a Ea] [b Eb];simpl;apply rec_lim_lim.
- intros;apply (rec_hprop I).
Defined.

Definition C_rec@{} (I : Recursors) : C T -> A
  := C_rect _ _ _ (recursors_inductors I).

Definition equiv_rec@{} I
  : forall x y e, close e x y -> B e (C_rec I x) (C_rec I y)
  := @equiv_rect _ _ _ _ (recursors_inductors I).

Definition C_rec_eta@{} I q : C_rec I (eta q) = rec_eta I q
  := idpath.

Definition C_rec_lim@{} I x : C_rec I (lim x) =
  rec_lim I x (fun e => C_rec I (x e))
    (fun d e => equiv_rec I _ _ _ (approx_equiv x d e))
  := idpath.

End mutual_recursion.

Section equiv_alt.

Definition balls@{} := sigT@{Ularge UQ}
  (fun half : C T -> Q+ -> TruncType@{UQ} -1 =>
  (forall u e, half u e <-> merely (exists d d', e = d + d' /\ half u d))
  /\ (forall u v n e, close e u v -> half u n -> half v (n+e))).

Definition balls_close@{} e (R1 R2 : balls)
  := forall u n, (R1.1 u n -> R2.1 u (e+n)) /\ (R2.1 u n -> R1.1 u (e+n)).

Definition upper_cut@{} := sigT@{Ularge UQ}
  (fun R : Q+ -> TruncType@{UQ} -1 =>
    forall e, R e <-> merely (exists d d', e = d + d' /\ R d)).

Definition upper_cut_close@{} e (R1 R2 : upper_cut)
  := forall n, (R1.1 n -> R2.1 (e+n)) /\ (R2.1 n -> R1.1 (e+n)).

Lemma balls_separated' : forall u v,
  (forall e, balls_close e u v) -> u = v.
Proof.
intros u v E.
apply Sigma.path_sigma_hprop.
apply path_forall. intro x. apply path_forall. intro e.
apply TruncType.path_iff_hprop_uncurried.
unfold balls_close in E.
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

Definition balls_separated@{}
  := balls_separated'@{Ularge Uhuge}.

Instance balls_close_hprop@{}
  : forall e u v, IsHProp (balls_close e u v).
Proof.
unfold balls_close. intros. apply _.
Qed.

Definition equiv_alt_eta_eta@{} (q r : T) : upper_cut.
Proof.
exists (fun e => BuildhProp (close e q r)).
simpl. intro. apply rounded.
Defined.

Lemma eta_lim_rounded_step@{} :
  forall val_ind : Q+ -> upper_cut,
  (forall d e : Q+, upper_cut_close (d + e) (val_ind d) (val_ind e)) ->
  forall e : Q+,
  merely (exists d d' : Q+, e = d + d' /\ (val_ind d).1 d')
  <-> merely (exists d d' : Q+,
     e = d + d' /\ merely (exists d0 d'0 : Q+, d = d0 + d'0 /\ (val_ind d0).1 d'0)).
Proof.
unfold upper_cut_close. intros a Ea e.
split;apply (Trunc_ind _);intros [d [d' [He E]]].
- generalize (fst ((a _).2 _) E);apply (Trunc_ind _).
  intros [n [n' [Hd' E1]]].
  apply tr;do 2 econstructor;split;
  [|apply tr;do 2 econstructor;split;[reflexivity|exact E1]].
  path_via (d+n+n').
  rewrite He,Hd'. apply pos_eq,plus_assoc.
- revert E;apply (Trunc_ind _);intros [n [n' [Hd E]]].
  apply tr;do 2 econstructor;split;[|eapply Ea,E].
  path_via (d'/2 + (n + d'/2 + n')).
  rewrite <-(pos_unconjugate 2 d') in He. rewrite He,Hd.
  apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_alt_eta_lim@{}
  : forall val_ind : Q+ -> upper_cut,
  (forall d e : Q+, upper_cut_close (d + e) (val_ind d) (val_ind e)) ->
  upper_cut.
Proof.
intros val_ind IH.
exists (fun e => merely (exists d d', e = d + d' /\ (val_ind d).1 d')).
apply eta_lim_rounded_step. trivial.
Defined.

Lemma upper_cut_separated' : forall x y : upper_cut,
  (forall e : Q+, upper_cut_close e x y) -> x = y.
Proof.
intros x y E.
unfold upper_cut,upper_cut_close in *;
apply Sigma.path_sigma_hprop.
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

Definition upper_cut_separated@{}
  := upper_cut_separated'@{Ularge Uhuge}.

Lemma equiv_alt_eta_eta_eta_pr@{} :
forall q q0 r (e : Q+),
close e q0 r
-> upper_cut_close e ((λ r0, equiv_alt_eta_eta q r0) q0)
    ((λ r0, equiv_alt_eta_eta q r0) r).
Proof.
unfold equiv_alt_eta_eta.
red;simpl. intros q r1 r2 e Hr n.
split.
- intros E;apply symmetry.
  apply symmetry in E;revert E;apply triangular. symmetry; trivial.
- intros E;apply symmetry.
  apply symmetry in E;revert E;apply triangular. trivial.
Qed.

Lemma equiv_alt_eta_eta_lim_pr@{} :
forall q q0 (d d' e : Q+) (y : Approximation (C T)) (b : Q+ -> upper_cut)
(Eb : forall d0 e0 : Q+, upper_cut_close (d0 + e0) (b d0) (b e0)),
e = d + d'
-> close d' (eta q0) (y d)
  -> upper_cut_close d' ((λ r, equiv_alt_eta_eta q r) q0) (b d)
    -> upper_cut_close e ((λ r, equiv_alt_eta_eta q r) q0)
        ((λ _ : Approximation (C T), equiv_alt_eta_lim) y b Eb).
Proof.
simpl;intros q r d d' e y b Eb He _ IH.
unfold equiv_alt_eta_eta in IH;simpl in IH.
intros e';split.
- intros E1.
  pose proof (fst (IH _) E1) as E2.
  apply tr. exists d, (d' + e').
  split;trivial.
  rewrite He. apply pos_eq;ring_tac.ring_with_nat.
- apply (Trunc_ind _). intros [n [n' [He' E1]]].
  pose proof (fst (Eb _ d _) E1) as E2.
  apply IH in E2. simpl in E2.
  rewrite He,He'.
  assert (Hrw : (d + d' + (n + n')) = (d' + (n + d + n')))
  by (apply pos_eq;ring_tac.ring_with_nat).
  rewrite Hrw;trivial.
Qed.

Lemma equiv_alt_eta_lim_eta_pr@{} :
forall q r (d d' e : Q+) (x : Approximation (C T)) (a : Q+ -> upper_cut)
(Ea : forall d0 e0 : Q+, upper_cut_close (d0 + e0) (a d0) (a e0)),
  e = d + d'
  -> close d' (x d) (eta r)
  -> upper_cut_close d' (a d) ((λ r0, equiv_alt_eta_eta q r0) r)
  -> upper_cut_close e ((λ _ : Approximation (C T), equiv_alt_eta_lim) x a Ea)
  ((λ r0, equiv_alt_eta_eta q r0) r).
Proof.
unfold upper_cut_close;simpl;intros q r d d' e x a Ea He xi IH e'.
split.
- apply (Trunc_ind _). intros [n [n' [He' E1]]].
  pose proof (fst (Ea _ d _) E1) as E2.
  apply IH in E2.
  rewrite He,He'.
  assert (Hrw : (d + d' + (n + n')) = (d' + (n + d + n')))
  by (apply pos_eq;ring_tac.ring_with_nat).
  rewrite Hrw;trivial.
- intros E1.
  pose proof (snd (IH _) E1) as E2.
  apply tr. exists d, (d' + e').
  split;trivial.
  rewrite He. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_eta_lim_lim_pr@{} :
forall (x y : Approximation (C T)) (a b : Q+ -> upper_cut)
(Ea : forall d e : Q+, upper_cut_close (d + e) (a d) (a e))
(Eb : forall d e : Q+, upper_cut_close (d + e) (b d) (b e)) (e d n n' : Q+),
e = d + n + n'
-> close n' (x d) (y n)
  -> upper_cut_close n' (a d) (b n)
    -> upper_cut_close e ((λ _, equiv_alt_eta_lim) x a Ea)
        ((λ _, equiv_alt_eta_lim) y b Eb).
Proof.
unfold upper_cut_close;simpl;intros x y a b Ea Eb e d n n' He xi IH.
intros e';split;apply (Trunc_ind _).
- intros [d0 [d0' [He' E1]]].
  apply tr.
  pose proof (fst (Ea _ d _) E1) as E2.
  apply (fst (IH _)) in E2.
  exists n, (n' + (d0 + d + d0')).
  split;trivial.
  rewrite He,He'. apply pos_eq; ring_tac.ring_with_nat.
- intros [d0 [d0' [He' E1]]].
  apply tr.
  pose proof (fst (Eb _ n _) E1) as E2.
  apply (snd (IH _)) in E2.
  exists d, (n' + (d0 + n + d0')).
  split;trivial.
  rewrite He,He'. apply pos_eq; ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_eta_ok@{} : forall (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
r (e : Q+),
merely (exists d d' : Q+, e = d + d' /\ (equiv_alt_x_e d).1 (eta r) d')
<-> merely
    (exists d d' : Q+,
     e = d + d'
     /\ merely
         (exists d0 d'0 : Q+, d = d0 + d'0 /\ (equiv_alt_x_e d0).1 (eta r) d'0)).
Proof.
intros a Ea r e.
split;apply (Trunc_ind _);intros [d [d' [He E]]].
- generalize (fst (fst (a _).2 _ _) E);apply (Trunc_ind _).
  intros [n [n' [Hd' E1]]].
  apply tr;do 2 econstructor;split;
  [|apply tr;do 2 econstructor;split;[reflexivity|exact E1]].
  path_via (d+n+n').
  rewrite He,Hd'. apply pos_eq,plus_assoc.
- revert E;apply (Trunc_ind _);intros [n [n' [Hd E]]].
  apply tr;do 2 econstructor;split;[|eapply Ea,E].
  path_via (d'/2 + (n + d'/2 + n')).
  rewrite <-(pos_unconjugate 2 d') in He. rewrite He,Hd.
  apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_alt_lim_eta@{} : forall (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(r : T), upper_cut.
Proof.
intros ???.
red. exists (fun e => merely (exists d d' : Q+, e = d + d' /\
  (equiv_alt_x_e d).1 (eta r) d')).
apply equiv_alt_lim_eta_ok;trivial.
Defined.

Lemma equiv_alt_lim_lim_ok@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(y : Approximation (C T))
(e : Q+)
  : merely (exists d d' n : Q+, e = d + d' + n /\ (equiv_alt_x_e d).1 (y n) d')
    <-> merely
    (exists d d' : Q+,
     e = d + d'
     /\ merely
         (exists d0 d'0 n : Q+, d = d0 + d'0 + n /\ (equiv_alt_x_e d0).1 (y n) d'0)).
Proof.
pose proof (fun e => (equiv_alt_x_e e).2) as E1.
red in IHx. simpl in E1.
split;apply (Trunc_ind _).
- intros [d [d' [n [He E2]]]].
  apply (merely_destruct (fst (fst (E1 _) _ _) E2)).
  intros [d0 [d0' [Hd' E3]]].
  apply tr;exists (d+d0+n);exists d0';split;
  [|apply tr;econstructor;econstructor;econstructor;split;[reflexivity|exact E3]].
  rewrite He,Hd'. apply pos_eq; ring_tac.ring_with_nat.
- intros [d [d' [He E2]]]. revert E2;apply (Trunc_ind _).
  intros [d0 [d0' [n [Hd E2]]]].
  pose proof (fun e u v n e0 xi => snd (E1 e) u v n e0 xi) as E3.
  pose proof (fun a b c c' => E3 c _ _ c' _ (approx_equiv y a b)) as E4;clear E3.
  pose proof (fun a => E4 _ a _ _ E2) as E3. clear E4.
  rewrite Hd in He.
  apply tr;repeat econstructor;[|exact (E3 (d' / 2))].
  path_via (d0 + d0' + n + (2 / 2) * d').
  + rewrite pos_recip_r,Qpos_mult_1_l.
    trivial.
  + apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_alt_lim_lim@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(y : Approximation (C T)) : upper_cut.
Proof.
red.
exists (fun e => merely (exists d d' n, e = d + d' + n /\
  (equiv_alt_x_e d).1 (y n) d')).
apply equiv_alt_lim_lim_ok. trivial.
Defined.

Lemma equiv_alt_lim_lim_eta_lim_eta_pr@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(q r : T) (e : Q+)
(He : close e q r)
  : upper_cut_close e (equiv_alt_lim_eta equiv_alt_x_e IHx q)
    (equiv_alt_lim_eta equiv_alt_x_e IHx r).
Proof.
red. unfold equiv_alt_lim_eta;simpl. red in IHx.
pose proof (fun e => (equiv_alt_x_e e).2) as equiv_alt_x_e_pr.
simpl in equiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d [d' [Hn E1]]].
  pose proof (equiv_eta_eta _ _ _ _ He) as E2.
  pose proof (snd (equiv_alt_x_e_pr _) _ _ _ _ E2 E1) as E3.
  apply tr;exists d, (d'+e);split;[|exact E3].
  rewrite Hn. apply pos_eq;ring_tac.ring_with_nat.
- intros [d [d' [Hn E1]]].
  pose proof (equiv_eta_eta _ _ _ _ He) as E2.
  apply symmetry in E2.
  pose proof (snd (equiv_alt_x_e_pr _) _ _ _ _ E2 E1) as E3.
  apply tr;exists d, (d'+e);split;[|exact E3].
  rewrite Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_lim_eta_lim_lim_pr@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(q : T) (d d' e : Q+) (y : Approximation (C T)) (b : Q+ -> upper_cut)
(IHb : forall d0 e0 : Q+, upper_cut_close (d0 + e0) (b d0) (b e0))
(He : e = d + d')
(xi : close d' (eta q) (y d))
  : upper_cut_close d' (equiv_alt_lim_eta equiv_alt_x_e IHx q) (b d) ->
    upper_cut_close e (equiv_alt_lim_eta equiv_alt_x_e IHx q)
              (equiv_alt_lim_lim equiv_alt_x_e IHx y).
Proof.
unfold upper_cut_close,equiv_alt_lim_eta,equiv_alt_lim_lim;simpl;intros E1.
pose proof (fun e => (equiv_alt_x_e e).2) as equiv_alt_x_e_pr.
simpl in equiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d0 [d0' [Hn E2]]].
  pose proof (snd (equiv_alt_x_e_pr _) _ _ _ _ xi E2) as E3.
  apply tr;do 3 econstructor;split;[|exact E3].
  rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
- intros [d0 [d0' [n0 [Hn E2]]]].
  pose proof (fun a b => snd (equiv_alt_x_e_pr a) _ _ b _ (symmetry _ _ xi)) as E3.
  pose proof (fun a b a' b' => (snd (equiv_alt_x_e_pr a) _ _ b _
    (symmetry _ _ (approx_equiv y a' b')))) as E4.
  pose proof (fun a => E4 _ _ a _ E2) as E5. clear E4.
  pose proof (E3 _ _ (E5 _)) as E4. clear E3 E5.
  apply tr;do 2 econstructor;split;[|exact E4].
  rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_lim_lim_lim_eta_pr@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(r : T) (d d' e : Q+) (x : Approximation (C T)) (a : Q+ -> upper_cut)
(IHa : forall d0 e0 : Q+, upper_cut_close (d0 + e0) (a d0) (a e0))
(He : e = d + d')
(xi : close d' (x d) (eta r))
  : upper_cut_close d' (a d) (equiv_alt_lim_eta equiv_alt_x_e IHx r) ->
    upper_cut_close e (equiv_alt_lim_lim equiv_alt_x_e IHx x)
              (equiv_alt_lim_eta equiv_alt_x_e IHx r).
Proof.
unfold upper_cut_close,equiv_alt_lim_eta,equiv_alt_lim_lim;simpl;intros E1.
pose proof (fun e => (equiv_alt_x_e e).2) as equiv_alt_x_e_pr.
simpl in equiv_alt_x_e_pr.
intros n;split;apply (Trunc_ind _).
- intros [d0 [d0' [n0 [Hn E2]]]].
  pose proof (fun a b => (snd (equiv_alt_x_e_pr a) _ _ b _ xi) ) as E3.
  pose proof (fun a b a' b' => (snd (equiv_alt_x_e_pr a) _ _ b _
    (approx_equiv x a' b'))) as E4.
  pose proof (fun a => E4 _ _ _ a E2) as E5. clear E4.
  pose proof (E3 _ _ (E5 _)) as E4. clear E3 E5.
  apply tr;do 2 econstructor;split;[|exact E4].
  rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
- intros [d0 [d0' [Hn E2]]].
  pose proof (snd (equiv_alt_x_e_pr _) _ _ _ _ (symmetry _ _ xi) E2) as E3.
  apply tr;do 3 econstructor;split;[|exact E3].
  rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_lim_lim_lim_lim_pr@{} (equiv_alt_x_e : Q+ -> balls)
(IHx : forall d e : Q+, balls_close (d + e)
  (equiv_alt_x_e d) (equiv_alt_x_e e))
(x y : Approximation (C T)) (a b : Q+ -> upper_cut)
(IHa : forall d e : Q+, upper_cut_close (d + e) (a d) (a e))
(IHb : forall d e : Q+, upper_cut_close (d + e) (b d) (b e))
(e d n e' : Q+)
(He : e = d + n + e')
(xi : close e' (x d) (y n))
(IH : upper_cut_close e' (a d) (b n))
  : upper_cut_close e (equiv_alt_lim_lim equiv_alt_x_e IHx x)
              (equiv_alt_lim_lim equiv_alt_x_e IHx y).
Proof.
red in IH. red. unfold equiv_alt_lim_lim;simpl.
clear IH IHa IHb a b.
pose proof (fun e => (equiv_alt_x_e e).2) as equiv_alt_x_e_pr.
simpl in equiv_alt_x_e_pr.
intros n0;split;apply (Trunc_ind _);intros [d0 [d' [n1 [Hn0 E1]]]].
- pose proof (fun f g => (snd (equiv_alt_x_e_pr f) _ _ g _ xi)) as E2.
  pose proof (fun f g h i => (snd (equiv_alt_x_e_pr f) _ _ g _
    (approx_equiv x h i))) as E3.
  pose proof (E2 _ _ (E3 _ _ _ _ E1)) as E4.
  apply tr;do 3 econstructor;split;[|exact E4].
  rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
- pose proof (fun f g => (snd (equiv_alt_x_e_pr f) _ _ g _ (symmetry _ _ xi)))
    as E2.
  pose proof (fun f g h i => (snd (equiv_alt_x_e_pr f) _ _ g _
    (symmetry _ _ (approx_equiv y h i)))) as E3.
  pose proof (E2 _ _ (E3 _ _ _ _ E1)) as E4.
  apply tr;do 3 econstructor;split;[|exact E4].
  rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma upper_cut_to_balls_second@{}
  (I : Recursors@{Ularge UQ} upper_cut upper_cut_close)
  (R := C_rec upper_cut upper_cut_close I
    : C T -> upper_cut)
  : forall (u v : C T) (n e : Q+),
    close e u v
    -> ((R u).1 n -> (R v).1 (n + e)) /\ ((R v).1 n -> (R u).1 (n + e)).
Proof.
pose proof (equiv_rec upper_cut upper_cut_close I) as R_pr.
red in R_pr.
change (C_rec upper_cut upper_cut_close I) with R in R_pr.
intros u v n e xi.
rewrite !(qpos_plus_comm n).
apply (R_pr u v e xi n).
Qed.

Definition upper_cut_to_balls@{}
  : Recursors@{Ularge UQ} upper_cut upper_cut_close -> balls.
Proof.
intros I.
pose (R := C_rec upper_cut upper_cut_close I).
exists (fun r => (R r).1).
split.
- exact (fun u => (R u).2).
- apply upper_cut_to_balls_second.
Defined.

Instance upper_cut_close_hprop@{} : forall e a b,
  IsHProp (upper_cut_close e a b).
Proof.
unfold upper_cut_close;apply _.
Qed.

Definition equiv_alt_eta@{} : T -> balls.
Proof.
intros q. apply upper_cut_to_balls.
simple refine (Build_Recursors upper_cut upper_cut_close
  _ _ upper_cut_separated upper_cut_close_hprop _ _ _ _).
- intros r. apply (equiv_alt_eta_eta q r).
- intros _. apply equiv_alt_eta_lim.
- exact (equiv_alt_eta_eta_eta_pr q).
- exact (equiv_alt_eta_eta_lim_pr q).
- exact (equiv_alt_eta_lim_eta_pr q).
- exact equiv_alt_eta_lim_lim_pr.
Defined.

Definition equiv_alt_eta_lim_compute@{} : forall q x e,
  paths@{Ularge} ((equiv_alt_eta q).1 (lim x) e)
  (merely (exists d d', e = d + d' /\ (equiv_alt_eta q).1 (x d) d')).
Proof.
reflexivity.
Defined.

Definition equiv_alt_lim@{} : forall (equiv_alt_x_e : Q+ -> balls),
  (forall d e : Q+, balls_close (d + e)
    (equiv_alt_x_e d) (equiv_alt_x_e e)) -> balls.
Proof.
intros equiv_alt_x_e IHx.
(* forall e u n, Requiv_alt_x_e e u n means Requiv_alt n (x e) u *)
apply upper_cut_to_balls.
simple refine (Build_Recursors upper_cut upper_cut_close
  _ _ upper_cut_separated upper_cut_close_hprop _ _ _ _).
- exact (equiv_alt_lim_eta _ IHx).
- intros y _ _;exact (equiv_alt_lim_lim equiv_alt_x_e IHx y).
- apply equiv_alt_lim_lim_eta_lim_eta_pr.
- simpl. apply equiv_alt_lim_lim_eta_lim_lim_pr.
- simpl. apply equiv_alt_lim_lim_lim_lim_eta_pr.
- simpl. apply equiv_alt_lim_lim_lim_lim_lim_pr.
Defined.

Lemma equiv_alt_lim_lim_compute@{} : forall (a : Q+ -> balls) Ea x e,
  paths@{Ularge} ((equiv_alt_lim a Ea).1 (lim x) e)
  (merely (exists d d' n, e = d + d' + n /\
    (a d).1 (x n) d')).
Proof.
reflexivity.
Defined.

Lemma equiv_alt_eta_eta_pr@{} : forall (q r : T) (e : Q+), close e q r ->
  balls_close e (equiv_alt_eta q) (equiv_alt_eta r).
Proof.
intros q r e Hqr.
red. apply (C_ind0 (fun u => forall n, _)).
- simpl. split; apply triangular; trivial. symmetry;trivial.
- intros x Ex n.
  rewrite !equiv_alt_eta_lim_compute.
  split;apply (Trunc_ind _);intros [d [d' [Hn E1]]].
  + apply Ex in E1. apply tr;do 2 econstructor;split;[|exact E1].
    rewrite Hn. apply pos_eq;ring_tac.ring_with_nat.
  + apply Ex in E1. apply tr;do 2 econstructor;split;[|exact E1].
    rewrite Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_eta_lim_pr@{} : forall (q : T) (d d' e : Q+) (y : Approximation (C T))
(b : Q+ -> balls)
(Eb : forall d0 e0 : Q+, balls_close (d0 + e0) (b d0) (b e0)),
e = d + d'
-> close d' (eta q) (y d)
  -> balls_close d' (equiv_alt_eta q) (b d)
    -> balls_close e (equiv_alt_eta q) (equiv_alt_lim b Eb).
Proof.
intros q d d' e y b Eb He xi IH.
red. apply (C_ind0 (fun u => forall n, _)).
- simpl. intros q0 n.
  red in IH. pose proof (fun x => IH (eta x)) as E1.
  simpl in E1. clear IH. split.
  + intros E2.
    apply E1 in E2. apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He;apply pos_eq;ring_tac.ring_with_nat.
  + apply (Trunc_ind _);intros [d0 [d0' [Hn E2]]].
    rewrite He.
    assert (Hrw : (d + d' + n) = d' + (d + n))
    by (apply pos_eq;ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    apply E1.
    rewrite Hn.
    red in Eb.
    pose proof (fst (Eb _ d _ _) E2) as E3.
    assert (Hrw : (d + (d0 + d0')) = (d0 + d + d0'))
    by (apply pos_eq;ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    trivial.
- intros x Ex n.
  rewrite !equiv_alt_eta_lim_compute,!equiv_alt_lim_lim_compute.
  split;apply (Trunc_ind _).
  + intros [d0 [d0' [Hn E1]]].
    apply IH in E1.
    apply tr;do 3 econstructor;split;[|exact E1].
    rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
  + intros [d0 [d0' [n0 [Hn E1]]]].
    red in Eb. pose proof (fst (Eb _ d _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_eta_pr@{} : forall (r : T) (d d' e : Q+) (x : Approximation (C T))
(a : Q+ -> balls)
(Ea : forall d0 e0 : Q+, balls_close (d0 + e0) (a d0) (a e0)),
e = d + d'
-> close d' (x d) (eta r)
  -> balls_close d' (a d) (equiv_alt_eta r)
    -> balls_close e (equiv_alt_lim a Ea) (equiv_alt_eta r).
Proof.
intros r d d' e x a Ea He xi IH.
red. apply (C_ind0 (fun u => forall n, _)).
- simpl. intros q n;split.
  + apply (Trunc_ind _). intros [d0 [d0' [Hn E1]]].
    pose proof (fun x => fst (Ea _ x _ _) E1) as E2.
    pose proof (fst (IH _ _) (E2 _)) as E3.
    simpl in E3.
    rewrite He,Hn.
    assert (Hrw : (d + d' + (d0 + d0')) = (d' + (d0 + d + d0')))
    by (apply pos_eq;ring_tac.ring_with_nat);rewrite Hrw;clear Hrw.
    trivial.
  + intros E1.
    red in IH.
    pose proof (snd (IH (eta _) _) E1) as E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He. apply pos_eq;ring_tac.ring_with_nat.
- intros y Ey n.
  rewrite !equiv_alt_eta_lim_compute,!equiv_alt_lim_lim_compute.
  split;apply (Trunc_ind _).
  + intros [d0 [d0' [n0 [Hn E1]]]].
    pose proof (fun x => fst (Ea _ x _ _) E1) as E2.
    pose proof (fst (IH _ _) (E2 _)) as E3.
    apply tr;do 2 econstructor;split;[|exact E3].
    rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
  + intros [d0 [d0' [Hn E1]]].
    pose proof (snd (IH _ _) E1) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Lemma equiv_alt_lim_lim_pr@{} : forall (x y : Approximation (C T))
  (a b : Q+ -> balls)
  (Ea : forall d e : Q+, balls_close (d + e) (a d) (a e))
  (Eb : forall d e : Q+, balls_close (d + e) (b d) (b e)) (e d n e' : Q+),
  e = d + n + e'
  -> close e' (x d) (y n)
  -> balls_close e' (a d) (b n)
  -> balls_close e (equiv_alt_lim a Ea) (equiv_alt_lim b Eb).
Proof.
intros x y a b Ea Eb e d n e' He xi IH.
red. apply (C_ind0 (fun u => forall n0, _)).
- intros q n0.
  simpl. split;apply (Trunc_ind _).
  + intros [d0 [d' [Hn0 E1]]].
    pose proof (fst (Ea _ d _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
  + intros [d0 [d' [Hn0 E1]]].
    pose proof (fst (Eb _ n _ _) E1) as E2.
    apply IH in E2.
    apply tr;do 2 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
- intros z Ez n0.
  simpl.
  split;apply (Trunc_ind _).
  + intros [d0 [d' [n1 [Hn0 E1]]]].
    pose proof (fst (IH _ _) (fst (Ea _ _ _ _) E1)) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
  + intros [d0 [d' [n1 [Hn0 E1]]]].
    pose proof (snd (IH _ _) (fst (Eb _ _ _ _) E1)) as E2.
    apply tr;do 3 econstructor;split;[|exact E2].
    rewrite He,Hn0. apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_alt_balls@{} : C T -> balls.
Proof.
apply (C_rec balls balls_close).
apply (Build_Recursors balls balls_close
  equiv_alt_eta (fun _ => equiv_alt_lim)
  balls_separated balls_close_hprop).
- exact equiv_alt_eta_eta_pr.
- exact equiv_alt_eta_lim_pr.
- exact equiv_alt_lim_eta_pr.
- exact equiv_alt_lim_lim_pr.
Defined.

Definition equiv_alt : Q+ -> C T -> C T -> Type
  := fun e x y => (equiv_alt_balls x).1 y e.

Definition equiv_alt_eta_eta_def@{} : forall e q r,
  paths@{Ularge} (equiv_alt e (eta q) (eta r)) (close e q r).
Proof.
intros;exact idpath.
Defined.

Definition equiv_alt_eta_lim_def@{} : forall e q y,
  paths@{Ularge} (equiv_alt e (eta q) (lim y))
  (merely (exists d d', e = d + d' /\ equiv_alt d' (eta q) (y d))).
Proof.
intros;exact idpath.
Defined.

Definition equiv_alt_lim_eta_def@{} : forall e x r,
  paths@{Ularge} (equiv_alt e (lim x) (eta r))
  (merely (exists d d', e = d + d' /\ equiv_alt d' (x d) (eta r))).
Proof.
intros;exact idpath.
Defined.

Definition equiv_alt_lim_lim_def@{} : forall e x y,
  paths@{Ularge} (equiv_alt e (lim x) (lim y))
  (merely (exists d d' n, e = d + d' + n /\ equiv_alt d' (x d) (y n))).
Proof.
intros;exact idpath.
Defined.

Lemma equiv_alt_round@{} : @Rounded (C T) equiv_alt.
Proof.
hnf. intros. apply ((equiv_alt_balls u).2).
Qed.

Lemma equiv_alt_equiv@{} : forall u v w n e, equiv_alt n u v -> close e v w ->
  equiv_alt (n+e) u w.
Proof.
intros ????? E1 E2.
apply (snd (equiv_alt_balls u).2 _ _ _ _ E2). trivial.
Qed.

Lemma equiv_equiv_alt : forall u v w n e, close n u v -> equiv_alt e v w ->
  equiv_alt (n+e) u w.
Proof.
intros ????? E1 E2.
pose proof (fun x y => snd (equiv_alt_balls x).2 _ _ y _ E1).
(* do we need to prove Symmetric (Requiv_alt _)? *)
(* We don't actually need this lemma
   as we just rewrite Requiv_alt = Requiv in the previous one. *)
Abort.

Lemma equiv_to_equiv_alt' : forall e u v, close e u v -> equiv_alt e u v.
Proof.
apply (equiv_rec0 _).
- auto.
- intros q y e d d' He _ IH.
  rewrite equiv_alt_eta_lim_def. apply tr;eauto.
- intros;rewrite equiv_alt_lim_eta_def;apply tr;eauto.
- intros x y e d n e' He _ IH;rewrite equiv_alt_lim_lim_def.
  apply tr;do 3 econstructor;split;[|exact IH].
  rewrite He;apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_to_equiv_alt@{}
  := equiv_to_equiv_alt'@{UQ UQ UQ}.

Lemma equiv_alt_to_equiv' : forall e u v, equiv_alt e u v -> close e u v.
Proof.
intros e u v;revert u v e.
apply (C_ind0 (fun u => forall v e, _ -> _)).
- intros q;apply (C_ind0 (fun v => forall e, _ -> _)).
  + intros r e;rewrite equiv_alt_eta_eta_def.
    apply equiv_eta_eta.
  + intros x Ex e;rewrite equiv_alt_eta_lim_def.
    apply (Trunc_ind _);intros [d [d' [He E1]]].
    eapply equiv_eta_lim;eauto.
- intros x Ex;apply (C_ind0 (fun v => forall e, _ -> _)).
  + intros r e;rewrite equiv_alt_lim_eta_def.
    apply (Trunc_ind _);intros [d [d' [He E1]]].
    eapply equiv_lim_eta;eauto.
  + intros y Ey e;rewrite equiv_alt_lim_lim_def.
    apply (Trunc_ind _);intros [d [d' [n [He E1]]]].
    eapply equiv_lim_lim;[|eauto].
    rewrite He;apply pos_eq;ring_tac.ring_with_nat.
Qed.

Definition equiv_alt_to_equiv@{}
  := equiv_alt_to_equiv'@{UQ UQ UQ UQ}.

Lemma equiv_alt_rw' : equiv_alt = close.
Proof.
repeat (apply path_forall;intro);apply TruncType.path_iff_ishprop_uncurried.
split.
- apply equiv_alt_to_equiv.
- apply equiv_to_equiv_alt.
Qed.

Definition equiv_alt_rw@{}
  := equiv_alt_rw'@{Ularge}.

Lemma equiv_eta_eta_def' : forall e q r, close e (eta q) (eta r) = close e q r.
Proof.
rewrite <-equiv_alt_rw;trivial.
Qed.

Definition equiv_eta_eta_def@{}
  := equiv_eta_eta_def'@{Ularge UQ UQ}.

Lemma equiv_eta_lim_def' : forall e q y,
  close e (eta q) (lim y) =
  merely (exists d d', e = d + d' /\ close d' (eta q) (y d)).
Proof.
rewrite <-equiv_alt_rw;trivial.
Qed.

Definition equiv_eta_lim_def@{}
  := equiv_eta_lim_def'@{Ularge UQ UQ}.

Lemma equiv_lim_eta_def' : forall e x r,
  close e (lim x) (eta r) =
  merely (exists d d', e = d + d' /\ close d' (x d) (eta r)).
Proof.
rewrite <-equiv_alt_rw;trivial.
Qed.

Definition equiv_lim_eta_def@{}
  := equiv_lim_eta_def'@{Ularge UQ UQ}.

Lemma equiv_lim_lim_def' : forall e (x y : Approximation (C T)),
  close e (lim x) (lim y) =
  merely (exists d d' n, e = d + d' + n /\ close d' (x d) (y n)).
Proof.
rewrite <-equiv_alt_rw;trivial.
Qed.

Definition equiv_lim_lim_def@{}
  := equiv_lim_lim_def'@{Ularge UQ UQ}.

Lemma equiv_rounded' : Rounded (C T).
Proof.
hnf. rewrite <-equiv_alt_rw;exact equiv_alt_round.
Qed.

Definition equiv_rounded@{}
  := @equiv_rounded'@{UQ}.

Lemma equiv_triangle' : Triangular (C T).
Proof.
hnf;intros. rewrite <-equiv_alt_rw.
apply equiv_alt_equiv with v;trivial.
rewrite equiv_alt_rw;trivial.
Qed.

Definition equiv_triangle@{}
  := equiv_triangle'@{UQ UQ}.

End equiv_alt.

Existing Instance equiv_rounded.
Existing Instance equiv_triangle.

Global Instance C_premetric@{} : PreMetric (C T).
Proof.
split;apply _.
Qed.

Lemma C_equiv_through_approx@{} : forall u (y : Approximation (C T)) e d,
  close e u (y d) -> close (e+d) u (lim y).
Proof.
apply (C_ind0 (fun u => forall y e d, _ -> _)).
- intros q y e d E. eapply equiv_eta_lim;[apply qpos_plus_comm|].
  trivial.
- intros x Ex y e d xi.
  pose proof (fun e n => Ex n x e n (equiv_refl _ _)) as E1.
  generalize (fst (equiv_rounded _ _ _) xi);apply (Trunc_ind _).
  intros [d0 [d' [He E2]]].
  pose proof (equiv_triangle _ _ _ _ _ (E1 (d' / 2) (d' / 4)) E2) as E3.
  eapply equiv_lim_lim;[|exact E3].
  rewrite He.
  path_via (d0 + (4 / 4) * d' + d).
  { rewrite pos_recip_r,Qpos_mult_1_l. trivial. }
  assert (Hrw : 4 / 4 = 2 / 4 + 1 / 2 :> Q+).
  { rewrite two_fourth_is_one_half. rewrite pos_recip_r;path_via ((2/ 2) : Q+).
    { rewrite pos_recip_r;trivial. }
    { apply pos_eq;ring_tac.ring_with_nat. }
  }
  rewrite Hrw.
  apply pos_eq;ring_tac.ring_with_nat.
Qed.

Global Instance equiv_lim@{} : CauchyComplete (C T).
Proof.
red;red;intros. apply C_equiv_through_approx.
apply equiv_refl.
Qed.

Lemma unique_continuous_extension@{i j} {A:Type@{i} } `{Closeness A}
  `{!PreMetric@{i j} A}
  (f g : C T -> A)
  `{!Continuous f} `{!Continuous g}
  : (forall q, f (eta q) = g (eta q)) -> forall u, f u = g u.
Proof.
intros E.
apply (C_ind0 _).
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
  { apply equiv_rounded. apply tr;do 2 econstructor;split;[|
    apply equiv_symm,equiv_lim].
    path_via (nd/2 + n + nd/2).
    path_via (2 / 2 * nd + n).
    { rewrite pos_recip_r,Qpos_mult_1_l,qpos_plus_comm;trivial. }
    apply pos_eq;ring_tac.ring_with_nat.
  }
  assert (Hx' : close d' (lim x) (x n)).
  { apply equiv_rounded. apply tr;do 2 econstructor;split;[|
    apply equiv_symm,equiv_lim].
    path_via (nd'/2 + n + nd'/2).
    path_via (2 / 2 * nd' + n).
    { rewrite pos_recip_r,Qpos_mult_1_l,qpos_plus_comm;trivial. }
    apply pos_eq;ring_tac.ring_with_nat.
  }
  apply Ed in Hx. apply Ed' in Hx'.
  rewrite IHx in Hx.
  pose proof (triangular _ _ _ _ _ Hx (symmetry _ _ Hx')) as E1.
  rewrite (pos_split2 e). trivial.
Qed.

Global Instance eta_nonexpanding : NonExpanding eta.
Proof.
intros e x y.
apply equiv_eta_eta.
Qed.

Lemma C_eq_equiv@{} : forall u v : C T, u = v -> forall e, close e u v.
Proof.
intros u v [] e;apply (equiv_refl _).
Qed.

Lemma eta_injective@{} : Injective eta.
Proof.
intros q r E.
apply separated.
intros e. change (equiv_alt e (eta q) (eta r)).
apply equiv_to_equiv_alt.
apply C_eq_equiv. trivial.
Qed.

Global Existing Instance eta_injective.

Section lipschitz_extend.
Context `{PreMetric A} {Alim : Lim A} `{!CauchyComplete A}.
Variables (f : T -> A) (L : Q+).
Context {Ef : Lipschitz f L}.

Lemma lipschitz_extend_eta_lim@{} :
  forall (q : T) (d d' e : Q+) (b : Q+ -> A) Eequiv,
  e = d + d'
  -> close (L * d') (f q) (b d)
  -> close (L * e) (f q)
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / L);
         approx_equiv := Eequiv |}).
Proof.
simpl. intros q d d' e b Eequiv He IH.
assert (Hrw : L * e = L * d' + L * d)
  by (rewrite He;apply pos_eq;ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply equiv_through_approx.
simpl. rewrite (pos_unconjugate L d). apply IH.
Qed.

Lemma lipschitz_extend_lim_lim@{} :
  forall (a b : Q+ -> A) (e d n e' : Q+)
  Eequiv1 Eequiv2,
  e = d + n + e'
  -> close (L * e') (a d) (b n)
  -> close (L * e)
      (lim
         {|
         approximate := λ e0 : Q+, a (e0 / L);
         approx_equiv := Eequiv1 |})
      (lim
         {|
         approximate := λ e0 : Q+, b (e0 / L);
         approx_equiv := Eequiv2 |}).
Proof.
simpl;intros a b e d n e' ?? He IH.
apply premetric.equiv_lim_lim with (L * d) (L * n) (L * e').
+ rewrite He;apply pos_eq;ring_tac.ring_with_nat.
+ simpl. rewrite 2!pos_unconjugate. apply IH.
Qed.

Lemma lipschitz_extend_lim_pr@{} :
  forall (a : Q+ -> A)
  (Ea : forall d e : Q+, close (L * (d + e)) (a d) (a e)),
  forall d e : Q+, close (d + e) (a (d / L)) (a (e / L)).
Proof.
intros. pattern (d+e);eapply transport.
apply symmetry, (pos_recip_through_plus d e L).
apply Ea.
Qed.

Lemma separate_mult@{} : forall l (u v : A),
  (forall e, close (l * e) u v) -> u = v.
Proof.
intros l x y E. apply separated.
intros. assert (Hrw : e = l * (e / l)).
+ path_via ((l / l) * e).
   * rewrite pos_recip_r. apply symmetry,Qpos_mult_1_l.
   * apply pos_eq. ring_tac.ring_with_nat.
+ rewrite Hrw;apply E.
Qed.

Definition lipshitz_extend_recursor@{}
  : Recursors A (fun e x y => close (L * e) x y).
Proof.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _);simpl.
- exact f.
- intros _ a Ea.
  apply lim. exists (fun e => a (e / L)).
  apply lipschitz_extend_lim_pr. trivial.
- apply separate_mult.
- intros ???;apply Ef.
- simpl. intros ???? _ ??? _;apply lipschitz_extend_eta_lim;trivial.
- simpl;intros ???? _ ?? He _ IH.
  apply symmetry in IH;symmetry.
  revert He IH;apply lipschitz_extend_eta_lim;trivial.
- simpl. intros _ _ ????????? _;apply lipschitz_extend_lim_lim;trivial.
Defined.

Definition lipschitz_extend@{}
  : C T -> A
  := C_rec _ _ lipshitz_extend_recursor.

Global Instance lipschitz_extend_lipschitz@{} : Lipschitz lipschitz_extend L.
Proof.
intros ???;apply (equiv_rec _ _ lipshitz_extend_recursor).
Defined.

Definition lipschitz_extend_eta@{} q : lipschitz_extend (eta q) = f q
  := idpath.

Lemma lipschitz_extend_lim_approx@{} (x : Approximation (C T))
  : forall d e : Q+, close (d + e) (lipschitz_extend (x (d / L)))
                                 (lipschitz_extend (x (e / L))).
Proof.
exact (lipschitz_extend_lim_pr
                    (λ e, lipschitz_extend (x e))
                    (λ d e, equiv_rec _ _
                       lipshitz_extend_recursor (x d) (x e) (d + e)
                       (approx_equiv x d e))).
Defined.

Definition lipschitz_extend_lim@{} x
  : lipschitz_extend (lim x) =
    lim (Build_Approximation (fun e => lipschitz_extend (x (e / L)))
    (lipschitz_extend_lim_approx x))
  := idpath.

End lipschitz_extend.

Section lipschitz_extend_extra.
Universe UA UAQ.
Context {A:Type@{UA} } `{PreMetric@{UA UAQ} A}
  {Alim : Lim A} `{!CauchyComplete A}.

Global Instance lipschitz_extend_nonexpanding (f : T -> A) `{!NonExpanding f}
  : NonExpanding (lipschitz_extend f 1).
Proof.
apply (lipschitz_nonexpanding _).
Qed.

Lemma lipschitz_extend_same_distance@{} (f g : T -> A) (L:Q+)
  `{!Lipschitz f L} `{!Lipschitz g L} : forall e,
  (forall d q, close (e+d) (f q) (g q)) ->
  forall d u, close (e+d) (lipschitz_extend f L u) (lipschitz_extend g L u).
Proof.
intros e E1 d u;revert u d;apply (C_ind0@{UAQ} (fun u => forall d, _)).
- intros q d;apply E1.
- intros x Ex d. rewrite !lipschitz_extend_lim. revert d.
  apply lim_same_distance. simpl.
  intros;apply Ex.
Qed.

End lipschitz_extend_extra.

Section completion_of_complete.

Context {Tlim : Lim T} `{!CauchyComplete T}.

Definition completion_back@{} : C T -> T := lipschitz_extend id 1.

Definition eta_back@{} : forall x, eta (completion_back x) = x
  := unique_continuous_extension (compose eta completion_back) id
    (fun _ => idpath).

Definition back_eta@{} : forall x, completion_back (eta x) = x
  := fun _ => idpath.

Global Instance eta_isequiv : IsEquiv eta
  := BuildIsEquiv T _ eta completion_back eta_back back_eta
    (fun _ => path_ishprop _ _).

Definition eta_equiv : T <~> C T
  := BuildEquiv _ _ eta _.

Lemma C_of_complete' : C T = T :> Type@{UQ}.
Proof.
symmetry;apply path_universe with eta. apply _.
Defined.
Definition C_of_complete@{i} := C_of_complete'@{i UQ UQ}.

End completion_of_complete.

End generalities.

Section extend_binary.
Variables A B : Type@{UQ}.
Context {Aclose : Closeness A} {Bclose : Closeness B}
  {Apremetric : PreMetric A} {premetric : PreMetric B}
  {T:Type@{UQ} } `{Tclose : Closeness T} {Tpremetric : PreMetric T}
  {Clim : Lim T} `{!CauchyComplete T}.

Variable (f : A -> B -> T) (L1 L2 : Q+).
Context `{!forall q, Lipschitz (f q) L1}
  `{!forall s, Lipschitz (fun q => f q s) L2}.

Definition lipschitz_extend_binary_f_l1 : A -> C B -> T
  := fun q => lipschitz_extend B (f q) L1.

Instance lipschitz_extend_binary_f_l1_pr
  : Lipschitz lipschitz_extend_binary_f_l1 L2.
Proof.
intros e x y xi.
apply rounded in xi. revert xi;apply (Trunc_ind _).
intros [d [d' [He E]]].
apply tr. exists (L2*d),(L2*d');split.
+ rewrite He; apply Qpos_plus_mult_distr_l.
+ intros z. apply rounded in E;revert E;
  apply (Trunc_ind _);intros [n [n' [Hd E]]].
  rewrite Hd,Qpos_plus_mult_distr_l.
  apply lipschitz_extend_same_distance. intros n0 q.
  apply rounded_plus.
  apply (lipschitz (fun r => f r q) L2).
  trivial.
Qed.

Definition lipschitz_extend_binary@{} : C A -> C B -> T
  := lipschitz_extend A lipschitz_extend_binary_f_l1 L2.

Global Instance lipschitz_extend_binary_r@{}
  : forall w, Lipschitz (fun u => lipschitz_extend_binary u w) L2.
Proof.
pose proof (lipschitz_extend_lipschitz A lipschitz_extend_binary_f_l1 L2) as E.
intros w e u v xi.
apply E in xi.
apply close_arrow_apply,xi.
Qed.

Global Instance lipschitz_extend_binary_l@{}
  : forall u, Lipschitz (lipschitz_extend_binary u) L1.
Proof.
unfold lipschitz_extend_binary.
simple refine (C_ind0 A _ _ _);simpl.
- unfold Lipschitz;apply _.
- intros q. change (Lipschitz (lipschitz_extend_binary_f_l1 q) L1).
  unfold lipschitz_extend_binary_f_l1. apply _.
- intros s E. apply _.
Qed.

Definition lipschitz_extend_binary_eta@{} q v :
  lipschitz_extend_binary (eta q) v = lipschitz_extend _ (f q) L1 v
  := idpath.


Definition lipschitz_extend_binary_lim_pr (x : Approximation (C A)) (v : C B)
  (e d : Q+)
  : close (e + d)
    (lipschitz_extend_binary (x (e / L2)) v)
    (lipschitz_extend_binary (x (d / L2)) v).
Proof.
apply close_arrow_apply.
exact (lipschitz_extend_lim_approx A lipschitz_extend_binary_f_l1 L2 x e d).
Defined.

Definition lipschitz_extend_binary_lim@{} (x : Approximation (C A)) v :
  lipschitz_extend_binary (lim x) v =
  lim {| approximate := λ e : Q+,
          lipschitz_extend_binary (x (e / L2)) v
      ;  approx_equiv := lipschitz_extend_binary_lim_pr x v |}
  := idpath.

Definition lipschitz_extend_binary_eta_eta@{} q r :
  lipschitz_extend_binary (eta q) (eta r) = f q r
  := idpath.

End extend_binary.

Section completion_idempotent.
Variable T : Type@{UQ}.
Context {Tclose : Closeness T} {Tpremetric : PreMetric T}.

Definition C_idempotent@{i} : C (C T) = C T :> Type@{UQ}
  := C_of_complete@{i} _.

End completion_idempotent.

Section completion_prod.
Variables (A B : Type@{UQ}).
Context {Aclose : Closeness A} {Bclose : Closeness B}
  `{!PreMetric A} `{!PreMetric B}.

Definition completion_fst@{} : C (A /\ B) -> C A
  := lipschitz_extend _ (eta ∘ fst) 1.

Definition completion_snd@{} : C (A /\ B) -> C B
  := lipschitz_extend _ (eta ∘ snd) 1.

Definition completion_pair@{} : C (A /\ B) -> C A /\ C B
  := fun s => (completion_fst s, completion_snd s).

Definition pair_completion@{} : C A -> C B -> C (A /\ B)
  := lipschitz_extend_binary _ _ (fun x y => eta (pair x y)) 1 1.

Instance completion_pair_continuous@{} : Continuous completion_pair.
Proof.
change (Continuous (uncurry pair ∘ map2 completion_fst completion_snd ∘ BinaryDup)).
apply _.
Qed.

Global Instance completion_pair_isequiv@{} : IsEquiv completion_pair.
Proof.
simple refine (BuildIsEquiv _ _ _ (uncurry pair_completion) _ _ _).
- hnf. unfold uncurry. intros [a b];simpl;revert a.
  apply (unique_continuous_extension _ _ _).
  intros q. revert b. apply (unique_continuous_extension _ _ _).
  intros r. reflexivity.
- hnf. apply (unique_continuous_extension _ _ _).
  intros q;reflexivity.
- intros. apply path_ishprop.
Defined.

Definition completion_pair_equiv@{} : C (A /\ B) <~> (C A /\ C B)
  := BuildEquiv _ _ completion_pair _.

Lemma completion_prod_rw : C (A /\ B) = (C A /\ C B) :> Type@{UQ}.
Proof.
apply path_universe_uncurried. apply completion_pair_equiv.
Defined.

End completion_prod.


