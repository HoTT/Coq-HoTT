Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.HSet
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders.

Coercion trunctype_type : TruncType >-> Sortclass.
Coercion equiv_fun : Equiv >-> Funclass.

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

Section contents.
Context `{Funext} `{Univalence}.

Section basics.
Variable A : Type.
Context `{IsHSet A}.

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
  Tle (delay_rec R x) (delay_rec R y)
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

Definition delayLe_ind0 (P : forall a b : delay A, a <= b -> Type)
  {sP : forall a b E, IsHProp (P a b E)}
  (val_refl : forall a, P a a (delay_refl A a))
  (val_bot_least : forall b, P (bot A) b (bot_least A b))
  (val_sup_le_l : forall f p x E, P _ _ E -> forall n, P _ _ (sup_le_l A f p x E n))
  (val_sup_le_r : forall f p x E, (forall n, P _ _ (E n)) ->
    P _ _ (sup_le_r A f p x E))
  : forall a b E, P a b E.
Proof.
apply (delayLe_rect A (fun _ => Unit) (fun a b _ _ E => P a b E)).
split;simpl;auto.
intros;apply path_ishprop.
Defined.

Definition eta_le_recursors (a : A) : Recursors hProp (fun P Q => P -> Q).
Proof.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros b. exists (a = b). apply _.
- exists Empty;apply _.
- intros f p. exact (merely (exists n, f n)).
- trivial.
- intros _ [].
- simpl. intros s p x E n En. apply E. apply tr;exists n;trivial.
- simpl. intros s p x E. apply (Trunc_ind _);intros [n En]. apply (E n En).
- hnf. intros. apply TruncType.path_iff_hprop_uncurried. split;trivial.
Defined.

Definition sim_le_recursors
  : Recursors (delay A -> hProp) (fun P Q => forall x, Q x -> P x).
Proof.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros a. apply (delay_rec _ _ (eta_le_recursors a)).
- intros _;exists Unit;apply _.
- intros f p x. exists (forall n, f n x). apply _.
- trivial.
- simpl. trivial.
- simpl. auto.
- simpl. auto.
- hnf;intros. apply path_forall. intros ?.
  apply TruncType.path_iff_hprop_uncurried. split;auto.
Defined.

Definition sim_le : delay A -> delay A -> hProp
  := delay_rec _ _ sim_le_recursors.

Lemma sim_to_le : forall a b, sim_le a b -> a <= b.
Proof.
apply (delay_ind0 (fun a => forall b, _ -> _)).
- intros a. apply (delay_ind0 (fun b => _ -> _)).
  + intros b;simpl. intros []. reflexivity.
  + simpl. intros [].
  + intros f p E1.
    change (merely (exists n, sim_le (eta A a) (f n)) -> eta A a <= sup A f p).
    apply (Trunc_ind _);intros [n E2].
    apply E1 in E2. transitivity (f n);trivial.
    apply sup_le_l with p. reflexivity.
- simpl. intros b _;apply bot_least.
- intros f p IH b. change ((forall n, sim_le (f n) b) -> sup A f p <= b).
  intros E. apply sup_le_r. intros n;apply IH;trivial.
Qed.

Lemma le_sim_le_trans : forall a b, a <= b -> forall c, sim_le b c -> sim_le a c.
Proof.
exact (delayLe_rec _ _ sim_le_recursors).
Qed.

Lemma sim_le_sup : forall f p x n, sim_le x (f n) -> sim_le x (sup A f p).
Proof.
intros f p;apply (delay_ind0 (fun x => forall n, _ -> _)).
- intros a n E. apply tr;exists n;apply E.
- simpl. trivial.
- intros g q IH n E.
  change (forall m, sim_le (g m) (sup A f p)). intros m.
  apply IH with n. apply le_sim_le_trans with (sup A g q).
  + apply sup_le_l with q. reflexivity.
  + trivial.
Qed.

Lemma sim_le_refl : forall a, sim_le a a.
Proof.
apply (delay_ind0 _).
- reflexivity.
- simpl;trivial.
- intros f p IH. change (forall n, sim_le (f n) (sup A f p)).
  intros n. apply sim_le_sup with n. trivial.
Qed.

Lemma le_to_sim : forall a b, a <= b -> sim_le a b.
Proof.
apply (delayLe_ind0 _).
- apply sim_le_refl.
- simpl. trivial.
- intros f p x E IH;exact IH.
- intros f p x E IH;exact IH.
Qed.

Lemma le_sim_rw : @le (delay A) _ = sim_le.
Proof.
apply path_forall;intros a;apply path_forall;intros b.
apply (ap trunctype_type).
apply TruncType.path_iff_hprop_uncurried. simpl. split.
- apply le_to_sim.
- apply sim_to_le.
Qed.

Lemma not_eta_le_bot : forall a, ~ eta A a <= bot A.
Proof.
intros a. rewrite le_sim_rw. simpl. red;trivial.
Qed.

Lemma eta_le_eta : forall a b, eta A a <= eta A b -> a = b.
Proof.
intros a b;rewrite le_sim_rw;trivial.
Qed.

Global Instance eta_injective : Injective (eta A).
Proof.
intros a b E. apply eta_le_eta. rewrite E;reflexivity.
Qed.

Lemma eta_le_sup : forall a f p, eta A a <= sup A f p ->
  merely (exists n, eta A a <= f n).
Proof.
intros a f p. rewrite le_sim_rw. trivial.
Qed.

Lemma sup_is_ub : forall f p n, f n <= sup A f p.
Proof.
intros f p n;apply sup_le_l with p. reflexivity.
Qed.

End basics.

Section monad.

Definition bind_recursors {A B} : (A -> delay B) ->
  Recursors A (delay B) le.
Proof.
intros f.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
- exact f.
- exact (bot B).
- intros s p. exact (sup B s p).
- reflexivity.
- apply bot_least.
- simpl. apply sup_le_l.
- simpl. apply sup_le_r.
Defined.

Definition bind {A B} : delay A -> (A -> delay B) -> delay B
  := fun x f => delay_rec _ _ _ (bind_recursors f) x.

Definition bind_le {A B} : forall (f : A -> delay B) a b, a <= b ->
  bind a f <= bind b f
  := fun f a b E => delayLe_rec _ _ _ (bind_recursors f) a b E.

Definition bind_eta_l {A B} : forall a f, bind (B:=B) (eta A a) f = f a
  := fun _ _ => idpath.

Definition bind_bot_l {A B} : forall f, bind (bot A) f = bot B
  := fun _ => idpath.

Definition bind_sup_l {A B} : forall f s p,
  bind (sup A s p) f = sup B (fun n => bind (s n) f) (fun n => bind_le f _ _ (p n))
  := fun _ _ _ => idpath.

Lemma sup_extensionality {A} : forall f p g q, (forall n, f n = g n) ->
  sup A f p = sup A g q.
Proof.
intros f p g q E.
apply (antisymmetry le).
- apply sup_le_r. intros n. rewrite E. apply sup_is_ub.
- apply sup_le_r. intros n. rewrite <-E. apply sup_is_ub.
Qed.

Definition bind_eta_r {A} : forall x, bind x (eta A) = x.
Proof.
apply (delay_ind0 _ _);try reflexivity.
intros f p IH.
change (bind (sup A f p) (eta A)) with
  (sup A (λ n : nat, bind (f n) (eta A))
    (λ n : nat, bind_le (eta A) (f n) (f (S n)) (p n))).
apply sup_extensionality. trivial.
Defined.

Lemma bind_assoc {A B C} : forall x f g, bind (B:=C) (bind (A:=A) (B:=B) x f) g =
  bind x (fun a => bind (f a) g).
Proof.
intros x f g;revert x;apply (delay_ind0 _ _).
- reflexivity.
- reflexivity.
- intros s p IH.
  change (sup C (λ n, bind (bind (s n) f) g)
  (λ n, bind_le g (bind (s n) f) (bind (s (S n)) f)
     (bind_le f (s n) (s (S n)) (p n))) =
  sup C (λ n, bind (s n) (λ a, bind (f a) g))
    (λ n, bind_le (λ a, bind (f a) g) (s n) (s (S n)) (p n))).
  apply sup_extensionality. apply IH.
Defined.

End monad.

End contents.
