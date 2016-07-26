Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.HSet
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders.

Module Export Delay.

Section VarSec.

Variable A : Type.

Private Inductive delay : Type :=
  | eta : A -> delay
  | bot : Bottom delay
  | sup : forall f : nat -> delay, (forall n, f n <= f (S n)) -> delay

with delayLe : Le delay :=
  | delay_refl : Reflexive delayLe
  | bot_least : forall x, bot <= x
  | sup_le_l : forall f p x, sup f p <= x -> forall n, f n <= x
  | sup_le_r : forall f p x, (forall n, f n <= x) -> sup f p <= x
.
Axiom delay_antisymm : AntiSymmetric delayLe.
Axiom delayLe_hprop : is_mere_relation delay delayLe.

Global Existing Instance delayLe.
Global Existing Instance delayLe_hprop.

Section Induction.

Variables (P : delay -> Type)
  (Q : forall x y (u : P x) (v : P y), x <= y -> Type).

Record Inductors :=
  { ind_eta : forall x, P (eta x)
  ; ind_bot : P bot
  ; ind_sup : forall f p (If : forall n, P (f n))
      (Ip : forall n, Q (f n) (f (S n)) (If n) (If (S n)) (p n)),
      P (sup f p)
  ; ind_refl : forall x u, Q x x u u (delay_refl x)
  ; ind_bot_least : forall x v, Q bot x ind_bot v (bot_least x)
  ; ind_sup_le_l : forall f p x E If Ip u, Q (sup f p) x (ind_sup f p If Ip) u E ->
    forall n, Q (f n) x (If n) u (sup_le_l f p x E n)
  ; ind_sup_le_r : forall f p x E If Ip u, (forall n, Q (f n) x (If n) u (E n)) ->
    Q (sup f p) x (ind_sup f p If Ip) u (sup_le_r f p x E)

  ; ind_antisymm : forall x y u v E1 E2, Q x y u v E1 -> Q y x v u E2 ->
    delay_antisymm x y E1 E2 # u = v
  ; ind_prop : forall x y u v E, IsHProp (Q x y u v E)
  }.

Definition delay_rect : Inductors -> forall x, P x :=
  fun I x =>
  fix delay_rect (x : delay) {struct x} : Inductors -> P x :=
    match x return (Inductors -> P x) with
    | eta x => fun I => ind_eta I x
    | bot => fun I => ind_bot I
    | sup f p => fun I => ind_sup I f p (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
    end

  with delayLe_rect (x y : delay) (E : x <= y) {struct E}
    : forall I : Inductors, Q x y (delay_rect x I) (delay_rect y I) E :=
    match E in delayLe x' y'
    return (forall I : Inductors, Q x' y' (delay_rect x' I) (delay_rect y' I) E)
    with
    | delay_refl x => fun I => ind_refl I x (delay_rect x I)
    | bot_least x => fun I =>
      ind_bot_least I x (delay_rect x I)
    | sup_le_l f p x E n => fun I =>
      ind_sup_le_l I f p x E (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
        (delay_rect x I)
        (delayLe_rect _ _ E I) n
    | sup_le_r f p x E => fun I =>
      ind_sup_le_r I f p x E (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
        (delay_rect x I)
        (fun n => delayLe_rect _ _ (E n) I)
    end

  for delay_rect x I.

Definition delayLe_rect : forall (I : Inductors) (x y : delay) (E : x <= y),
  Q x y (delay_rect I x) (delay_rect I y) E
  := fun I x y E =>
  fix delay_rect (x : delay) {struct x} : Inductors -> P x :=
    match x return (Inductors -> P x) with
    | eta x => fun I => ind_eta I x
    | bot => fun I => ind_bot I
    | sup f p => fun I => ind_sup I f p (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
    end

  with delayLe_rect (x y : delay) (E : x <= y) {struct E}
    : forall I : Inductors, Q x y (delay_rect x I) (delay_rect y I) E :=
    match E in delayLe x' y'
    return (forall I : Inductors, Q x' y' (delay_rect x' I) (delay_rect y' I) E)
    with
    | delay_refl x => fun I => ind_refl I x (delay_rect x I)
    | bot_least x => fun I =>
      ind_bot_least I x (delay_rect x I)
    | sup_le_l f p x E n => fun I =>
      ind_sup_le_l I f p x E (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
        (delay_rect x I)
        (delayLe_rect _ _ E I) n
    | sup_le_r f p x E => fun I =>
      ind_sup_le_r I f p x E (fun n => delay_rect (f n) I)
        (fun n => delayLe_rect _ _ (p n) I)
        (delay_rect x I)
        (fun n => delayLe_rect _ _ (E n) I)
    end

  for delayLe_rect x y E I.

End Induction.

End VarSec.

End Delay.

Section basics.
Context `{Funext} `{Univalence}.

Variable A : Type.

Section Recursion.

Variables (T : Type) (Tle : T -> T -> Type).

Record Recursors :=
  { rec_eta : A -> T
  ; rec_bot : T
  ; rec_sup : forall (f : nat -> T) (p : forall n, Tle (f n) (f (S n))), T

  ; rec_refl : forall x : T, Tle x x
  ; rec_bot_least : forall x : T, Tle rec_bot x
  ; rec_sup_le_l : forall s p x, Tle (rec_sup s p) x -> forall n, Tle (s n) x
  ; rec_sup_le_r : forall s p x, (forall n, Tle (s n) x) -> Tle (rec_sup s p) x

  ; rec_antisymm : AntiSymmetric Tle
  ; rec_prop : is_mere_relation T Tle }.

Definition recursors_inductors
  : Recursors -> Inductors A (fun _ => T) (fun _ _ x y _ => Tle x y).
Proof.
intros R. simple refine (Build_Inductors A _ _
  (rec_eta R) (rec_bot R) (fun _ _ => rec_sup R) _ _ _ _ _ _);simpl.
- intros _;exact (rec_refl R).
- intros _;exact (rec_bot_least R).
- intros _ _ _ _. exact (rec_sup_le_l R).
- intros _ _ _ _. exact (rec_sup_le_r R).
- intros. rewrite PathGroupoids.transport_const. apply (rec_antisymm R);trivial.
- intros _ _ ?? _;exact (rec_prop R _ _).
Defined.

Definition delay_rec : Recursors -> delay A -> T
  := fun R => delay_rect _ _ _ (recursors_inductors R).

Definition delayLe_rec : forall (R : Recursors) (x y : delay A) (E : x <= y),
  delay_rec R x <= delay_rec R y
  := fun R => delayLe_rect _ _ _ (recursors_inductors R).

End Recursion.

Definition delayLe_rect0 (P : forall x y : delay A, x <= y -> Type)
  {sP : forall x y E, IsHProp (P x y E)}
  (val_refl : forall x, P x x (delay_refl A x))
  (val_bot_least : forall x, P _ _ (bot_least A x))
  (val_sup_le_l : forall f p x E (Ip : forall n, P (f n) (f (S n)) (p n)),
    P (sup A f p) x E -> forall n, P (f n) x (sup_le_l A f p x E n))
  (val_sup_le_r : forall f p x E (Ip : forall n, P (f n) (f (S n)) (p n)),
    (forall n, P (f n) x (E n)) -> P (sup A f p) x (sup_le_r A f p x E))
  : forall x y E, P x y E.
Proof.
apply (delayLe_rect A (fun _ => Unit) (fun x y _ _ E => P x y E)).
split;simpl;auto;simpl.
intros. apply path_ishprop.
Defined.

Lemma delayLe_trans : Transitive (@le (delay A) _).
Proof.
hnf. intros x y z E;revert x y E z.
apply (delayLe_rect0 (fun x y _ => forall z, _ -> _)).
- auto.
- intros;apply bot_least.
- intros;eapply sup_le_l;eauto.
- intros;apply sup_le_r;auto.
Qed.

Global Instance delay_set : IsHSet (delay A).
Proof.
apply (@HSet.isset_hrel_subpaths _ (fun x y => x <= y /\ y <= x)).
- intros x;split;apply delay_refl.
- apply _.
- intros x y E;apply delay_antisymm;apply E.
Qed.

Global Instance delay_order : PartialOrder (@le (delay A) _).
Proof.
repeat (split;try apply _).
- apply delay_refl.
- apply delayLe_trans.
Qed.

Definition delay_ind0 (P : delay A -> Type) {sP : forall x, IsHProp (P x)}
  (val_eta : forall x, P (eta A x))
  (val_bot : P (bot A))
  (val_sup : forall f p, (forall n, P (f n)) -> P (sup A f p))
  : forall x, P x.
Proof.
apply (delay_rect A _ (fun _ _ _ _ _ => Unit)).
split;simpl;auto.
- intros;apply path_ishprop.
- apply _.
Defined.

End basics.




