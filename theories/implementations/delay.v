Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
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
  ; ind_bot_least : forall x u v, Q bot x u v (bot_least x)
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
      ind_bot_least I x (ind_bot I) (delay_rect x I)
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
      ind_bot_least I x (ind_bot I) (delay_rect x I)
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

