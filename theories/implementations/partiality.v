Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
  HoTT.HSet
  HoTTClasses.interfaces.abstract_algebra
  HoTTClasses.interfaces.orders
  HoTTClasses.interfaces.monad
  HoTTClasses.implementations.peano_naturals.

Local Set Universe Minimization ToSet.

Coercion trunctype_type : TruncType >-> Sortclass.
Coercion equiv_fun : Equiv >-> Funclass.

Record IncreasingSequence A {Ale : Le A} :=
  { seq : nat -> A
  ; seq_increasing : forall n, seq n <= seq (S n) }.
Coercion seq : IncreasingSequence >-> Funclass.

Arguments Build_IncreasingSequence {A Ale} seq seq_increasing.
Arguments seq {A Ale} _ _.
Arguments seq_increasing {A Ale} _ _.

Global Instance seq_increasing_le `{PartialOrder A} (s : IncreasingSequence A)
  : OrderPreserving (seq s).
Proof.
hnf. intros a b E;induction E as [|b IH].
- reflexivity.
- transitivity (s b);trivial. apply seq_increasing.
Qed.

Module Export Partial.

Section VarSec.
Universe i.
Variable A : Type@{i}.

Private Inductive partial@{} : Type@{i} :=
  | eta : A -> partial
  | bot : Bottom partial
  | sup' : forall f : nat -> partial, (forall n, f n <= f (S n)) -> partial

with partialLe@{} : Le partial :=
  | partial_refl : Reflexive partialLe
  | bot_least : forall x, bot <= x
  | sup'_le_l : forall f p x, sup' f p <= x -> forall n, f n <= x
  | sup'_le_r : forall f p x, (forall n, f n <= x) -> sup' f p <= x
.
Axiom partial_antisymm : AntiSymmetric partialLe.
Axiom partialLe_hprop : is_mere_relation partial partialLe.

Global Existing Instance partialLe.
Global Existing Instance partialLe_hprop.

Definition sup@{} : IncreasingSequence partial -> partial
  := fun s => sup' s (seq_increasing s).

Definition sup_le_l@{} : forall (s : IncreasingSequence partial) x,
  sup s <= x -> forall n, s n <= x
  := fun s => sup'_le_l s (seq_increasing s).

Definition sup_le_r@{} : forall (s : IncreasingSequence partial) x,
  (forall n, s n <= x) -> sup s <= x
  := fun s => sup'_le_r s (seq_increasing s).

Section Induction.
Universe UP UQ.
Variables (P : partial -> Type@{UP})
  (Q : forall x y (u : P x) (v : P y), x <= y -> Type@{UQ}).

Record Inductors@{} :=
  { ind_eta : forall x, P (eta x)
  ; ind_bot : P bot
  ; ind_sup : forall (s : IncreasingSequence partial) (If : forall n, P (s n))
      (Ip : forall n, Q (s n) (s (S n)) (If n) (If (S n)) (seq_increasing s n)),
      P (sup s)
  ; ind_refl : forall x u, Q x x u u (partial_refl x)
  ; ind_bot_least : forall x v, Q bot x ind_bot v (bot_least x)
  ; ind_sup_le_l : forall f x E If Ip u, Q (sup f) x (ind_sup f If Ip) u E ->
    forall n, Q (f n) x (If n) u (sup_le_l f x E n)
  ; ind_sup_le_r : forall f x E If Ip u, (forall n, Q (seq f n) x (If n) u (E n)) ->
    Q (sup f) x (ind_sup f If Ip) u (sup_le_r f x E)

  ; ind_antisymm : forall x y u v E1 E2, Q x y u v E1 -> Q y x v u E2 ->
    partial_antisymm x y E1 E2 # u = v
  ; ind_prop : forall x y u v E, IsHProp (Q x y u v E)
  }.

Definition partial_rect@{} : Inductors -> forall x, P x :=
  fun I x =>
  fix partial_rect (x : partial) {struct x} : Inductors -> P x :=
    match x return (Inductors -> P x) with
    | eta x => fun I => ind_eta I x
    | bot => fun I => ind_bot I
    | sup' f p => fun I => ind_sup I (Build_IncreasingSequence f p)
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
    end

  with partialLe_rect (x y : partial) (E : x <= y) {struct E}
    : forall I : Inductors, Q x y (partial_rect x I) (partial_rect y I) E :=
    match E in partialLe x' y'
    return (forall I : Inductors, Q x' y' (partial_rect x' I) (partial_rect y' I) E)
    with
    | partial_refl x => fun I => ind_refl I x (partial_rect x I)
    | bot_least x => fun I =>
      ind_bot_least I x (partial_rect x I)
    | sup'_le_l f p x E n => fun I =>
      ind_sup_le_l I (Build_IncreasingSequence f p) x E
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
        (partial_rect x I)
        (partialLe_rect _ _ E I) n
    | sup'_le_r f p x E => fun I =>
      ind_sup_le_r I (Build_IncreasingSequence f p) x E
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
        (partial_rect x I)
        (fun n => partialLe_rect _ _ (E n) I)
    end

  for partial_rect x I.

Definition partialLe_rect@{} : forall (I : Inductors) (x y : partial) (E : x <= y),
  Q x y (partial_rect I x) (partial_rect I y) E
  := fun I x y E =>
  fix partial_rect (x : partial) {struct x} : Inductors -> P x :=
    match x return (Inductors -> P x) with
    | eta x => fun I => ind_eta I x
    | bot => fun I => ind_bot I
    | sup' f p => fun I => ind_sup I (Build_IncreasingSequence f p)
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
    end

  with partialLe_rect (x y : partial) (E : x <= y) {struct E}
    : forall I : Inductors, Q x y (partial_rect x I) (partial_rect y I) E :=
    match E in partialLe x' y'
    return (forall I : Inductors, Q x' y' (partial_rect x' I) (partial_rect y' I) E)
    with
    | partial_refl x => fun I => ind_refl I x (partial_rect x I)
    | bot_least x => fun I =>
      ind_bot_least I x (partial_rect x I)
    | sup'_le_l f p x E n => fun I =>
      ind_sup_le_l I (Build_IncreasingSequence f p) x E
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
        (partial_rect x I)
        (partialLe_rect _ _ E I) n
    | sup'_le_r f p x E => fun I =>
      ind_sup_le_r I (Build_IncreasingSequence f p) x E
        (fun n => partial_rect (f n) I)
        (fun n => partialLe_rect _ _ (p n) I)
        (partial_rect x I)
        (fun n => partialLe_rect _ _ (E n) I)
    end

  for partialLe_rect x y E I.

End Induction.

End VarSec.

End Partial.

Section contents.
Context `{Funext} `{Univalence}.

Section basics.
Universe UA.
Variable A : Type@{UA}.
Context `{IsHSet A}.

Section Recursion.
Universe UT UTle.
Variables (T : Type@{UT}) (Tle : T -> T -> Type@{UTle}).

Record Recursors@{} :=
  { rec_eta : A -> T
  ; rec_bot : T
  ; rec_sup : forall (f : nat -> T) (p : forall n, Tle (f n) (f (S n))), T

  ; rec_refl : forall x : T, Tle x x
  ; rec_bot_least : forall x : T, Tle rec_bot x
  ; rec_sup_le_l : forall s p x, Tle (rec_sup s p) x -> forall n, Tle (s n) x
  ; rec_sup_le_r : forall s p x, (forall n, Tle (s n) x) -> Tle (rec_sup s p) x

  ; rec_antisymm : AntiSymmetric Tle
  ; rec_prop : is_mere_relation T Tle }.

Definition recursors_inductors@{}
  : Recursors -> Inductors A (fun _ => T) (fun _ _ x y _ => Tle x y).
Proof.
intros R. simple refine (Build_Inductors A _ _
  (rec_eta R) (rec_bot R) (fun _ => rec_sup R) _ _ _ _ _ _);simpl.
- intros _;exact (rec_refl R).
- intros _;exact (rec_bot_least R).
- intros _ _ _. exact (rec_sup_le_l R).
- intros _ _ _. exact (rec_sup_le_r R).
- intros. rewrite PathGroupoids.transport_const. apply (rec_antisymm R);trivial.
- intros _ _ ?? _;exact (rec_prop R _ _).
Defined.

Definition partial_rec@{} : Recursors -> partial A -> T
  := fun R => partial_rect _ _ _ (recursors_inductors R).

Definition partialLe_rec@{} : forall (R : Recursors) (x y : partial A) (E : x <= y),
  Tle (partial_rec R x) (partial_rec R y)
  := fun R => partialLe_rect _ _ _ (recursors_inductors R).

Definition partial_rec_eta (R : Recursors) (a : A)
  : partial_rec R (eta A a) = rec_eta R a
  := idpath.

Definition partial_rec_sup (R : Recursors) (s : IncreasingSequence (partial A))
  : partial_rec R (sup A s) =
    rec_sup R (fun n => partial_rec R (s n))
      (fun n => partialLe_rec R _ _ (seq_increasing s n))
  := idpath.

End Recursion.

Definition partialLe_rect0@{UP} (P : forall x y : partial A, x <= y -> Type@{UP})
  {sP : forall x y E, IsHProp (P x y E)}
  (val_refl : forall x, P x x (partial_refl A x))
  (val_bot_least : forall x, P _ _ (bot_least A x))
  (val_sup_le_l : forall f x E
    (Ip : forall n, P (seq f n) (f (S n)) (seq_increasing f n)),
    P (sup A f) x E -> forall n, P (f n) x (sup_le_l A f x E n))
  (val_sup_le_r : forall f x E
    (Ip : forall n, P (seq f n) (f (S n)) (seq_increasing f n)),
    (forall n, P (f n) x (E n)) -> P (sup A f) x (sup_le_r@{UA} A f x E))
  : forall x y E, P x y E.
Proof.
apply (partialLe_rect@{UA Set UP} A (fun _ => Unit) (fun x y _ _ E => P x y E)).
split;simpl;auto;simpl.
intros.
pose proof @trunc_contr@{Set Set} as trunc_contr. (* Universe trick *)
apply path_ishprop.
Defined.

Lemma partialLe_trans@{} : Transitive (@le (partial@{UA} A) _).
Proof.
hnf. intros x y z E;revert x y E z.
apply (partialLe_rect0 (fun x y _ => forall z, _ -> _)).
- auto.
- intros;apply bot_least.
- intros;eapply sup_le_l;eauto.
- intros;apply sup_le_r;auto.
Qed.

Global Instance partial_set@{} : IsHSet (partial@{UA} A).
Proof.
apply (@HSet.isset_hrel_subpaths _ (fun x y => x <= y /\ y <= x)).
- intros x;split;apply partial_refl.
- apply _.
- intros x y E;apply partial_antisymm;apply E.
Qed.

Global Instance partial_order@{} : PartialOrder (@le (partial A) _).
Proof.
repeat (split;try apply _).
- apply partial_refl.
- apply partialLe_trans.
Qed.

Definition partial_ind0@{UP} (P : partial@{UA} A -> Type@{UP})
  {sP : forall x, IsHProp (P x)}
  (val_eta : forall x, P (eta A x))
  (val_bot : P (bot A))
  (val_sup : forall f, (forall n, P (seq f n)) -> P (sup A f))
  : forall x, P x.
Proof.
apply (partial_rect@{UA UP Set} A _ (fun _ _ _ _ _ => Unit)).
split;simpl;auto.
- intros;
  pose proof @trunc_contr@{Set Set} as trunc_contr. (* Universe trick *)
  apply path_ishprop.
- pose proof @trunc_contr@{Set Set} as trunc_contr. (* Universe trick *)
  apply _.
Defined.

Definition partialLe_ind0@{UP}
  (P : forall a b : partial@{UA} A, a <= b -> Type@{UP})
  {sP : forall a b E, IsHProp (P a b E)}
  (val_refl : forall a, P a a (partial_refl A a))
  (val_bot_least : forall b, P (bot A) b (bot_least A b))
  (val_sup_le_l : forall f x E, P _ _ E -> forall n, P _ _ (sup_le_l A f x E n))
  (val_sup_le_r : forall f x E, (forall n, P _ _ (E n)) ->
    P _ _ (sup_le_r A f x E))
  : forall a b E, P a b E.
Proof.
apply (partialLe_rect@{UA Set UP} A (fun _ => Unit) (fun a b _ _ E => P a b E)).
split;simpl;auto.
intros.
pose proof @trunc_contr@{Set Set} as trunc_contr. (* Universe trick *)
apply path_ishprop.
Defined.

Definition eta_le_recursors' (a : A)
  : Recursors@{Ularge Ularge} hProp (fun P Q => P -> Q).
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

Definition eta_le_recursors := eta_le_recursors'@{Uhuge}.

Definition sim_le_recursors'
  : Recursors@{Uhuge Ularge} (partial@{UA} A -> hProp)
    (fun P Q => forall x, Q x -> P x).
Proof.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _);simpl.
- intros a. apply (partial_rec _ _ (eta_le_recursors a)).
- intros _;exists Unit. apply trunc_succ.
- intros f p x. exists (forall n, f n x). apply _.
- trivial.
- simpl. trivial.
- simpl. auto.
- simpl. auto.
- hnf;intros. apply path_forall. intros ?.
  apply TruncType.path_iff_hprop_uncurried. split;auto.
Defined.

Definition sim_le_recursors@{} := sim_le_recursors'@{Ularge Uhuge}.

Definition sim_le@{} : partial A -> partial A -> hProp
  := partial_rec _ _ sim_le_recursors.

Lemma sim_to_le@{} : forall a b, sim_le a b -> a <= b.
Proof.
apply (partial_ind0 (fun a => forall b, _ -> _)).
- intros a. apply (partial_ind0 (fun b => _ -> _)).
  + intros b;simpl. intros []. reflexivity.
  + simpl. intros [].
  + intros f E1.
    change (merely (exists n, sim_le (eta A a) (f n)) -> eta A a <= sup A f).
    apply (Trunc_ind _);intros [n E2].
    apply E1 in E2. transitivity (f n);trivial.
    apply sup_le_l. reflexivity.
- simpl. intros b _;apply bot_least.
- intros f IH b. change ((forall n, sim_le (f n) b) -> sup A f <= b).
  intros E. apply sup_le_r. intros n;apply IH;trivial.
Qed.

Lemma le_sim_le_trans@{} : forall a b, a <= b -> forall c, sim_le b c -> sim_le a c.
Proof.
exact (partialLe_rec _ _ sim_le_recursors).
Qed.

Lemma sim_le_sup@{} : forall f x n, sim_le x (seq f n) -> sim_le x (sup A f).
Proof.
intros f;apply (partial_ind0@{Ularge} (fun x => forall n, _ -> _)).
- intros a n E. apply tr;exists n;apply E.
- simpl. trivial.
- intros g IH n E.
  change (forall m, sim_le (g m) (sup A f)). intros m.
  apply IH with n. apply le_sim_le_trans with (sup A g).
  + apply sup_le_l. reflexivity.
  + trivial.
Qed.

Lemma sim_le_refl@{} : forall a, sim_le a a.
Proof.
apply (partial_ind0 _).
- reflexivity.
- simpl;trivial.
- intros f IH. change (forall n, sim_le (f n) (sup A f)).
  intros n. apply sim_le_sup with n. trivial.
Qed.

Lemma le_to_sim@{} : forall a b, a <= b -> sim_le a b.
Proof.
apply (partialLe_ind0 _).
- apply sim_le_refl.
- simpl. trivial.
- intros f x E IH;exact IH.
- intros f x E IH;exact IH.
Qed.

Lemma le_sim_rw : @le (partial A) _ = sim_le.
Proof.
apply path_forall;intros a;apply path_forall;intros b.
apply (ap trunctype_type).
apply TruncType.path_iff_hprop_uncurried. simpl. split.
- apply le_to_sim.
- apply sim_to_le.
Qed.

Lemma not_eta_le_bot@{} : forall a, ~ eta@{UA} A a <= bot A.
Proof.
intros a E. apply le_to_sim in E;trivial.
Qed.

Lemma eta_le_eta@{} : forall a b, eta@{UA} A a <= eta A b -> a = b.
Proof.
intros a b;apply le_to_sim.
Qed.

Global Instance eta_injective@{} : Injective (eta@{UA} A).
Proof.
intros a b E. apply eta_le_eta. rewrite E;reflexivity.
Qed.

Lemma eta_le_sup@{} : forall a f, eta A a <= sup A f ->
  merely@{UA} (exists n, eta@{UA} A a <= f n).
Proof.
intros a f E. apply le_to_sim in E.
change (trunctype_type (merely (exists n, sim_le (eta A a) (f n)))) in E.
revert E;apply (Trunc_ind _);intros [n E].
apply tr;exists n;apply sim_to_le;trivial.
Qed.

Lemma sup_is_ub@{} : forall f n, seq f n <= sup@{UA} A f.
Proof.
intros f n;apply sup_le_l. reflexivity.
Qed.

Lemma eta_is_greatest : forall x a, eta A a <= x -> x = eta A a.
Proof.
apply (partial_ind0 (fun x => forall a, _ -> _)).
- intros ?? E;apply ap. Symmetry. apply eta_le_eta. trivial.
- intros a E. apply le_to_sim in E. destruct E.
- intros s IH a E.
  apply (antisymmetry le).
  + apply sup_le_r. intros n.
    apply eta_le_sup in E. revert E;apply (Trunc_ind _);intros [k E].
    destruct (total le n k) as [E1|E1].
    apply IH in E.
    * transitivity (s k).
      { apply (order_preserving _). trivial. }
      { rewrite E;reflexivity. }
    * rewrite (IH n a);[reflexivity|].
      transitivity (s k);trivial.
      apply (order_preserving _). trivial.
  + trivial.
Qed.

Lemma eta_eq_sup_iff : forall a s, sup A s = eta A a <->
  merely (exists n, s n = eta A a).
Proof.
intros a s;split.
- intros E.
  assert (E' : eta A a <= sup A s)
  by (rewrite E;reflexivity).
  generalize (eta_le_sup a s E').
  apply (Trunc_ind _);intros [n En].
  apply tr;exists n. apply (antisymmetry le).
  + apply sup_le_l. rewrite E;reflexivity.
  + trivial.
- apply (Trunc_ind _);intros [n En].
  apply eta_is_greatest. rewrite <-En. apply sup_is_ub.
Qed.

End basics.

Section monad.

Global Instance partial_ret@{i} : Return partial@{i} := eta.

Definition partial_bind_recursors@{i} {A B : Type@{i} } : (A -> partial@{i} B) ->
  Recursors A (partial@{i} B) le.
Proof.
intros f.
simple refine (Build_Recursors _ _ _ _ _ _ _ _ _ _ _ _);simpl.
- exact f.
- exact (bot B).
- intros s p. exact (sup' B s p).
- reflexivity.
- apply bot_least.
- simpl. apply sup'_le_l.
- simpl. apply sup'_le_r.
Defined.

Global Instance partial_bind : Bind partial
  := fun A B x f => partial_rec _ _ _ (partial_bind_recursors f) x.

Definition partial_bind_le {A B} : forall (f : A -> partial B) a b, a <= b ->
  bind a f <= bind b f
  := fun f a b E => partialLe_rec _ _ _ (partial_bind_recursors f) a b E.

Definition partial_bind_eta_l {A B} : forall a f, bind (B:=B) (eta A a) f = f a
  := fun _ _ => idpath.

Definition partial_bind_bot_l {A B} : forall f, bind (M:=partial) (bot A) f = bot B
  := fun _ => idpath.

Definition partial_bind_seq {A B} (f : A -> partial B) s :=
  Build_IncreasingSequence (fun n => bind (seq s n) f)
    (fun n => partial_bind_le f _ _ (seq_increasing s n)).

Definition partial_bind_sup_l {A B} : forall f s,
  bind (sup A s) f =
  sup B (partial_bind_seq f s).
Proof.
intros f s. change s with (Build_IncreasingSequence (seq s) (seq_increasing s)).
exact idpath.
Defined.

Lemma sup_extensionality {A} : forall f g, (forall n, seq f n = seq g n) ->
  sup A f = sup A g.
Proof.
intros f g E.
apply (antisymmetry le).
- apply sup_le_r. intros n. rewrite E. apply sup_is_ub.
- apply sup_le_r. intros n. rewrite <-E. apply sup_is_ub.
Qed.

Lemma sup_extensionality_tail {A} : forall f g, (forall n, seq f (S n) = seq g n) ->
  sup A f = sup A g.
Proof.
intros f g E.
apply (antisymmetry le).
- apply sup_le_r. intros n. transitivity (f (S n)).
  + apply seq_increasing.
  + rewrite E. apply sup_is_ub.
- apply sup_le_r. intros n. transitivity (f (S n)).
  + rewrite E. reflexivity.
  + apply sup_is_ub.
Qed.

Definition partial_bind_eta_r {A} : forall x, bind x (eta A) = x.
Proof.
apply (partial_ind0 _ _);try reflexivity.
intros f IH.
change (bind (sup A f) (eta A)) with
  (sup A (Build_IncreasingSequence
    (λ n : nat, bind (f n) (eta A))
    (λ n : nat, partial_bind_le (eta A) (f n) (f (S n)) (seq_increasing f n)))).
apply sup_extensionality. trivial.
Defined.

Lemma partial_bind_assoc {A B C} : forall x f g,
  bind (B:=C) (bind (A:=A) (B:=B) x f) g =
  bind x (fun a => bind (f a) g).
Proof.
intros x f g;revert x;apply (partial_ind0 _ _).
- reflexivity.
- reflexivity.
- intros s IH.
  change (sup C (partial_bind_seq g (partial_bind_seq f s)) =
    sup C (partial_bind_seq (λ a : A, bind (f a) g) s)).
  apply sup_extensionality. apply IH.
Defined.

Global Instance partial_monad : Monad partial.
Proof.
split.
- exact @partial_bind_eta_l.
- exact @partial_bind_eta_r.
- exact @partial_bind_assoc.
Qed.

End monad.

Section Fix.

Record MonotoneTransformer (A B : Type) :=
  { transform : (A -> partial B) -> A -> partial B
  ; transform_monotone : forall g1 g2, (forall x, g1 x <= g2 x) ->
      forall x, transform g1 x <= transform g2 x }.

Coercion transform : MonotoneTransformer >-> Funclass.

Context {A B : Type}.

Variable f : MonotoneTransformer A B.

Definition seq_transform : (A -> IncreasingSequence (partial B)) ->
  A -> IncreasingSequence (partial B).
Proof.
intros s x. exists (fun n => f (fun y => s y n) x).
intros n. apply transform_monotone. intros y. apply seq_increasing.
Defined.

Lemma repeat_increasing : forall n x,
  repeat n f (fun _ => bot _) x <= repeat (S n) f (fun _ => bot _) x.
Proof.
induction n.
- simpl;intros. apply bot_least.
- simpl. apply transform_monotone. trivial.
Defined.

Definition Fix_sequence : A -> IncreasingSequence (partial B).
Proof.
intros x. exists (fun n => repeat n f (fun _ => bot _) x).
intros;apply repeat_increasing.
Defined.

Definition Fix : A -> partial B := fun x => sup _ (Fix_sequence x).

End Fix.

Section Fix_pr.

Record ContinuousTransformer A B :=
  { cont_transform : MonotoneTransformer A B
  ; transform_continuous : forall (s : A -> IncreasingSequence (partial B)) x,
      cont_transform (compose (sup _) s) x =
      sup _ (seq_transform cont_transform s x) }.
Coercion cont_transform : ContinuousTransformer >-> MonotoneTransformer.

Context {A B : Type}.

Lemma Fix_pr : forall f : ContinuousTransformer A B, Fix f = f (Fix f).
Proof.
intros f. unfold Fix. apply path_forall. intros x.
rewrite transform_continuous. apply sup_extensionality_tail.
intros n. reflexivity.
Qed.

End Fix_pr.

End contents.
