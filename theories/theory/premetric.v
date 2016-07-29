Require Import
  HoTT.Types.Universe
  HoTT.Basics.Decidable
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
  HoTTClasses.theory.additional_operations.

Local Set Universe Minimization ToSet.

Section contents.
Context {funext : Funext} {univalence : Univalence}.

Class Closeness@{i} (A : Type@{i}) := close : Q+ -> relation@{i i} A.

Global Instance Q_close@{} : Closeness Q := fun e q r => - ' e < q - r < ' e.

Class Separated A `{Closeness A}
  := separated : forall x y, (forall e, close e x y) -> x = y :> A.

Class Triangular A `{Closeness A}
  := triangular : forall u v w e d, close e u v -> close d v w ->
  close (e+d) u w.

Class Rounded@{i j} (A:Type@{i}) `{Closeness A}
  := rounded : forall e u v, iff@{i j j} (close e u v)
    (merely@{j} (sigT@{UQ j} (fun d => sigT@{UQ j} (fun d' =>
      e = d + d' /\ close d u v)))).

Class PreMetric@{i j} (A:Type@{i}) {Aclose : Closeness A} :=
  { premetric_prop :> forall e, is_mere_relation A (close e)
  ; premetric_refl :> forall e, Reflexive (close (A:=A) e)
  ; premetric_symm :> forall e, Symmetric (close (A:=A) e)
  ; premetric_separated :> Separated A
  ; premetric_triangular :> Triangular A
  ; premetric_rounded :> Rounded@{i j} A }.

Lemma rounded_plus `{Rounded A} : forall d d' u v, close d u v ->
  close (d+d') u v.
Proof.
intros d d' u v xi;apply rounded.
apply tr;exists d,d';auto.
Qed.

Lemma rounded_le' `{Rounded A}
  : forall e u v, close e u v ->
  forall d, ' e <= ' d -> close d u v.
Proof.
intros e u v xi d E.
apply le_equiv_lt in E. destruct E as [E|E].
- apply pos_eq in E. rewrite <-E;trivial.
- pose proof (pos_eq _ (_ + _) (Qpos_diff_pr _ _ E)) as E'.
  rewrite E'. apply rounded_plus. trivial.
Qed.

Definition rounded_le@{i j} := @rounded_le'@{j i Ularge j}.
Arguments rounded_le {A _ _} e u v _ d _.

Section close_prod.
Universe UA UB i.
Context (A:Type@{UA}) (B:Type@{UB}) `{Closeness A} `{Closeness B}
  `{forall e, is_mere_relation A (close e)}
  `{forall e, is_mere_relation B (close e)}.

Global Instance close_prod@{} : Closeness@{i} (A /\ B)
  := fun e x y => close e (fst x) (fst y) /\ close e (snd x) (snd y).

Global Instance close_prod_refl@{}
  `{forall e, Reflexive (close (A:=A) e)}
  `{forall e, Reflexive (close (A:=B) e)}
  : forall e, Reflexive (close (A:=A /\ B) e).
Proof.
intros e;split;reflexivity.
Qed.

Global Instance close_prod_symm@{}
  `{forall e, Symmetric (close (A:=A) e)}
  `{forall e, Symmetric (close (A:=B) e)}
  : forall e, Symmetric (close (A:=A /\ B) e).
Proof.
intros e u v xi;split;Symmetry;apply xi.
Qed.

Global Instance close_prod_separated@{}
  `{!Separated A}
  `{!Separated B}
  : Separated (A /\ B).
Proof.
intros x y E.
apply Prod.path_prod;apply separated;intros;apply E.
Qed.

Global Instance close_prod_triangular@{}
  `{!Triangular A}
  `{!Triangular B}
  : Triangular (A /\ B).
Proof.
intros u v w e d E1 E2;split;(eapply triangular;[apply E1|apply E2]).
Qed.

Lemma close_prod_rounded'
  `{!Rounded A} 
  `{!Rounded B}
  : Rounded (A /\ B).
Proof.
intros e u v. split.
- intros [E0 E0'];apply rounded in E0;apply rounded in E0'.
  revert E0;apply (Trunc_ind _);intros [d1 [d1' [E1 E2]]].
  revert E0';apply (Trunc_ind _);intros [d2 [d2' [E3 E4]]].
  apply tr;exists (join d1 d2), (meet d1' d2');split.
  + rewrite E1. apply Qpos_sum_eq_join_meet. rewrite <-E1;trivial.
  + split.
    * apply rounded_le with d1;trivial.
      apply join_ub_l.
    * apply rounded_le with d2;trivial.
      apply join_ub_r.
- apply (Trunc_ind _);intros [d [d' [E1 E2]]].
  rewrite E1;split;apply rounded_plus,E2.
Qed.

Definition close_prod_rounded@{j} := @close_prod_rounded'@{j j j j j j}.
Arguments close_prod_rounded {_ _} _ _ _.
Global Existing Instance close_prod_rounded.

Lemma prod_premetric@{j} `{!PreMetric@{UA j} A} `{!PreMetric@{UB j} B}
  : PreMetric@{i j} (A /\ B).
Proof.
split;try apply _.
Qed.
Global Existing Instance prod_premetric.

End close_prod.

Class NonExpanding `{Closeness A} `{Closeness B} (f : A -> B)
  := non_expanding : forall e x y, close e x y -> close e (f x) (f y).
Arguments non_expanding {A _ B _} f {_ e x y} _.

Class Lipschitz `{Closeness A} `{Closeness B} (f : A -> B) (L : Q+)
  := lipschitz : forall e x y, close e x y -> close (L * e) (f x) (f y).
Arguments lipschitz {A _ B _} f L {_ e x y} _.

Class Uniform `{Closeness A} `{Closeness B} (f : A -> B) (mu : Q+ -> Q+)
  := uniform : forall e x y, close (mu e) x y -> close e (f x) (f y).
Arguments uniform {A _ B _} f mu {_} _ _ _ _.

Class Continuous@{UA UB}
  {A:Type@{UA} } `{Closeness A}
  {B:Type@{UB} } `{Closeness B} (f : A -> B)
  := continuous : forall u e, merely@{Ularge} (sigT@{UQ Ularge}
    (fun d => forall v, close d u v ->
    close e (f u) (f v))).
Arguments continuous {A _ B _} f {_} _ _.

Definition BinaryDup@{i} {A : Type@{i} } : A -> A /\ A := fun x => (x, x).
Definition uncurry {A B C} (f : A -> B -> C) : A /\ B -> C
  := fun x => f (fst x) (snd x).
Definition map2 {A B C D} (f : A -> C) (g : B -> D) : A /\ B -> C /\ D
  := fun x => (f (fst x), g (snd x)).

Section closeness.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.

Global Instance id_nonexpanding : NonExpanding (@id A).
Proof.
hnf;trivial.
Qed.

Global Instance BinaryDup_nonexpanding@{} : NonExpanding (@BinaryDup A).
Proof.
intros e x y E;split;exact E.
Qed.

Universe UB.
Context {B:Type@{UB} } `{Closeness B} (f : A -> B).

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

Global Instance lipschitz_const@{} `{forall e, Reflexive (close (A:=B) e)}
  : forall (b:B) (L:Q+), Lipschitz (fun _ : A => b) L.
Proof.
intros;hnf.
intros e _ _ _. reflexivity.
Qed.

Global Instance lipschitz_uniform@{} (L:Q+) `{!Lipschitz f L}
  : Uniform f (fun e => e / L) | 5.
Proof.
intros e u v xi.
rewrite <-(pos_unconjugate L e),<-Qpos_mult_assoc.
apply (lipschitz f L),xi.
Qed.

Lemma uniform_continuous@{} mu `{!Uniform@{UA UB} f mu} : Continuous f.
Proof.
hnf.
intros u e;apply tr;exists (mu e).
apply (uniform f mu).
Qed.
Global Existing Instance uniform_continuous | 5.

Definition lipschitz_continuous@{} (L:Q+) `{!Lipschitz f L} : Continuous f
  := _.

Definition nonexpanding_continuous@{} `{!NonExpanding f} : Continuous f
  := _.

End closeness.

Section compositions.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C} (g : B -> C) (f : A -> B).

Global Instance nonexpanding_compose@{}
  {Eg : NonExpanding g} {Ef : NonExpanding f}
  : NonExpanding (compose g f).
Proof.
hnf. intros e x y xi;exact (non_expanding g (non_expanding f xi)).
Qed.

Global Instance lipschitz_compose@{}
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
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L),commutativity. apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_r@{}
  L {Eg : Lipschitz g L} {Ef : NonExpanding f}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_r'@{Ularge} L.

Lemma lipschitz_compose_nonexpanding_l'
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L.
Proof.
rewrite <-(left_identity L). apply _.
Qed.

Global Instance lipschitz_compose_nonexpanding_l@{}
  L {Eg : NonExpanding g} {Ef : Lipschitz f L}
  : Lipschitz (compose g f) L
  := lipschitz_compose_nonexpanding_l'@{Ularge} L.

Lemma uniform_compose@{} mu {Eg : Uniform g mu} mu' {Ef : Uniform f mu'}
  : Uniform (compose g f) (compose mu' mu).
Proof.
intros e u v xi. unfold compose.
apply (uniform g _),(uniform f _),xi.
Qed.
Global Existing Instance uniform_compose.

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

Section currying.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C} `{!Triangular C}.

Global Instance uncurry_lipschitz (f : A -> B -> C) L1 L2
  `{!forall x, Lipschitz (f x) L1}
  `{!forall y, Lipschitz (fun x => f x y) L2}
  : Lipschitz (uncurry f) (L1 + L2).
Proof.
intros e [u1 u2] [v1 v2] [xi1 xi2]. simpl in xi1,xi2.
unfold uncurry;simpl.
assert (Hrw : (L1 + L2) * e = L1 * e + L2 * e)
by abstract (apply pos_eq;ring_tac.ring_with_nat);
rewrite Hrw;clear Hrw.
apply (triangular _ (f u1 v2)).
- apply (lipschitz _ L1). trivial.
- apply (lipschitz (fun u => f u v2) L2). trivial.
Qed.

Lemma uncurry_uniform
  `{!Rounded A} `{!Rounded B} (f : A -> B -> C) mu mu'
  `{!forall x, Uniform (f x) mu}
  `{!forall y, Uniform (fun x => f x y) mu'}
  : Uniform (uncurry f) (fun e => meet (mu (e/2)) (mu' (e/2))).
Proof.
intros e [u1 u2] [v1 v2] [xi1 xi2].
simpl in *.
rewrite (pos_split2 e).
apply (triangular _ (f u1 v2)).
- apply (uniform (f u1) _).
  eapply rounded_le.
  + exact xi2.
  + apply meet_lb_l.
- apply (uniform (fun v => f v v2) _).
  eapply rounded_le.
  + exact xi1.
  + apply meet_lb_r.
Qed.

End currying.

Section pair.
Universe UA.
Context {A:Type@{UA} } `{Closeness A} `{forall e, Reflexive (close (A:=A) e)}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B} `{forall e, Reflexive (close (A:=B) e)}.

Global Instance pair_nonexpanding_l : forall x, NonExpanding (@pair A B x).
Proof.
intros x e u v xi;split;simpl.
- reflexivity.
- exact xi.
Qed.

Global Instance pair_nonexpanding_r : forall y,
  NonExpanding (fun x => @pair A B x y).
Proof.
intros x e u v xi;split;simpl.
- exact xi.
- reflexivity.
Qed.

Global Instance fst_nonexpanding : NonExpanding (@fst A B).
Proof.
intros e u v xi;apply xi.
Qed.

Global Instance snd_nonexpanding : NonExpanding (@snd A B).
Proof.
intros e u v xi;apply xi.
Qed.

End pair.

Section prod_equiv.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.

Global Instance equiv_prod_symm_nonexpanding
  : NonExpanding (@Prod.equiv_prod_symm A B).
Proof.
intros e u v xi;split;apply xi.
Qed.

Global Instance equiv_prod_symm_inv_nonexpanding
  : NonExpanding ((@Prod.equiv_prod_symm A B)^-1).
Proof.
intros e u v xi;split;apply xi.
Qed.

Universe UC.
Context {C:Type@{UC} } `{Closeness C}.

Global Instance equiv_prod_assoc_nonexpanding
  : NonExpanding (@Prod.equiv_prod_assoc A B C).
Proof.
intros e u v xi;repeat split;apply xi.
Qed.

Global Instance equiv_prod_assoc_inc_nonexpanding
  : NonExpanding ((@Prod.equiv_prod_assoc A B C)^-1).
Proof.
intros e u v xi;repeat split;apply xi.
Qed.

End prod_equiv.

Section map2.
Universe UA.
Context {A:Type@{UA} } `{Closeness A}.
Universe UB.
Context {B:Type@{UB} } `{Closeness B}.
Universe UC.
Context {C:Type@{UC} } `{Closeness C}.
Universe UD.
Context {D:Type@{UD} } `{Closeness D}.
Variables (f : A -> C) (g : B -> D).

Lemma map2_nonexpanding'
  `{!NonExpanding f} `{!NonExpanding g}
  : NonExpanding (map2 f g).
Proof.
intros e u v xi;split;simpl; apply (non_expanding _),xi.
Qed.

Definition map2_nonexpanding@{i} := @map2_nonexpanding'@{i i}.
Arguments map2_nonexpanding {_ _} e x y xi.
Global Existing Instance map2_nonexpanding.

Lemma map2_lipschitz' `{!Rounded C} `{!Rounded D} Lf Lg
  `{!Lipschitz f Lf} `{!Lipschitz g Lg}
  : Lipschitz (map2 f g) (join Lf Lg).
Proof.
intros e u v xi. split;simpl.
- apply rounded_le with (Lf * e).
  + apply (lipschitz _ _),xi.
  + apply (order_preserving (.* ' e)).
    apply join_ub_l.
- apply rounded_le with (Lg * e).
  + apply (lipschitz _ _),xi.
  + apply (order_preserving (.* ' e)).
    apply join_ub_r.
Qed.

Definition map2_lipschitz@{i} := @map2_lipschitz'@{i i i i}.
Arguments map2_lipschitz {_ _} Lf Lg {_ _} e x y xi.
Global Existing Instance map2_lipschitz.

Lemma map2_continuous' `{!Rounded A} `{!Rounded B}
  `{!Continuous f} `{!Continuous g}
  : Continuous (map2 f g).
Proof.
intros u e.
apply (merely_destruct (continuous f (fst u) e));intros [d1 E1].
apply (merely_destruct (continuous g (snd u) e));intros [d2 E2].
apply tr;exists (meet d1 d2). intros v xi.
split;simpl.
- apply E1. apply rounded_le with (meet d1 d2).
  + apply xi.
  + apply meet_lb_l.
- apply E2. apply rounded_le with (meet d1 d2).
  + apply xi.
  + apply meet_lb_r.
Qed.

Definition map2_continuous@{i} := @map2_continuous'@{i i i i}.
Arguments map2_continuous {_ _ _ _} u e.
Global Existing Instance map2_continuous.

End map2.

Section interval.
Universe UA UALE.
Context {A:Type@{UA} } {Ale : Le@{UA UALE} A}.

Definition Interval a b := sigT (fun x : A => a <= x /\ x <= b).

Definition interval_proj a b : Interval a b -> A := pr1.

Context {Ameet : Meet A} {Ajoin : Join A}
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

Context `{Closeness A}.

Global Instance Interval_close (a b : A) : Closeness (Interval a b)
  := fun e x y => close e (interval_proj a b x) (interval_proj a b y).
Arguments Interval_close _ _ _ _ _ /.

(* NB: for some reason this forces UALE <= UA *)
Lemma Interval_premetric@{i} `{!PreMetric@{UA i} A} a b
  : PreMetric@{UA i} (Interval a b).
Proof.
split.
- unfold close;simpl. apply _.
- intros e u. red;red. reflexivity.
- intros e u v xi;red;red;Symmetry;apply xi.
- intros u v E.
  apply Sigma.path_sigma_hprop. apply separated,E.
- intros u v w e d xi1 xi2.
  red;red. apply (triangular _ (interval_proj a b v)).
  + exact xi1.
  + exact xi2.
- intros e u v. split.
  + intros xi. do 2 red in xi. apply (fst (rounded _ _ _)) in xi.
    exact xi.
  + intros E. unfold close,Interval_close in E. apply (snd (rounded _ _ _)) in E.
    exact E.
Qed.
Global Existing Instance Interval_premetric.

Global Instance interval_proj_nonexpanding (a b : A)
  : NonExpanding (interval_proj a b)
  := fun _ _ _ xi => xi.

End interval.

Section rationals.

Lemma Qclose_alt : forall e (q r : Q), close e q r <-> abs (q - r) < ' e.
Proof.
intros e q r;split.
- intros [E1 E2].
  destruct (total le 0 (q - r)) as [E|E].
  + rewrite (Qabs_of_nonneg _ E).
    trivial.
  + rewrite (Qabs_of_nonpos _ E).
    apply flip_lt_negate. rewrite involutive. trivial.
- intros E. split;[apply flip_lt_negate;rewrite involutive|];
  apply le_lt_trans with (abs (q - r));trivial.
  + apply Qabs_le_neg_raw.
  + apply Qabs_le_raw.
Qed.

Lemma Qclose_neg@{} : forall e (x y : Q), close e x y <-> close e (- x) (- y).
Proof.
intros e x y;split;intros E;apply Qclose_alt in E;apply Qclose_alt.
- rewrite <-(negate_plus_distr),Qabs_neg. trivial.
- rewrite <-(negate_plus_distr),Qabs_neg in E. trivial.
Qed.

Instance Q_close_symm@{} : forall e, Symmetric (@close Q _ e).
Proof.
red;unfold close;simpl.
intros e x y [E1 E2];split.
- apply flip_lt_negate. rewrite <-negate_swap_r,involutive.
  trivial.
- apply flip_lt_negate.
  rewrite negate_swap_r,involutive. trivial.
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
  assert (Hrw : s - r = q - r + (s - q))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat).
  rewrite Hrw;trivial.
- apply flip_lt_negate in E1.
  rewrite negate_swap_r,!involutive in E1.
  pose proof (plus_lt_compat _ _ _ _ E1 E2') as E.
  assert (Hrw : r - s = r - q + (q - s))
    by abstract ring_tac.ring_with_integers (NatPair.Z nat).
  rewrite Hrw;trivial.
Qed.

Instance Q_triangular@{} : Triangular Q.
Proof.
hnf. intros u v w e d E1 E2.
apply Q_triangular_one with v.
- Symmetry;trivial.
- trivial.
Qed.

Lemma Qclose_separating_not_lt : forall q r : Q, (forall e, close e q r) ->
  ~ q < r.
Proof.
intros q r E1 E2.
pose proof (E1 (Qpos_diff _ _ E2)) as E3. Symmetry in E3;apply Qclose_alt in E3.
unfold cast in E3;simpl in E3.
apply (irreflexivity lt (r - q)).
apply le_lt_trans with (abs (r - q));trivial.
apply Qabs_le_raw.
Qed.

Instance Qclose_separating : Separated Q.
Proof.
hnf. intros q r E1.
apply tight_apart. intros E2.
apply apart_iff_total_lt in E2. destruct E2 as [E2|E2].
- exact (Qclose_separating_not_lt _ _ E1 E2).
- refine (Qclose_separating_not_lt _ _ _ E2).
  intros;Symmetry;trivial.
Qed.

Instance Qclose_rounded@{} : Rounded Q.
Proof.
intros e q r;split.
- intros E;apply Qclose_alt in E.
  pose proof (Q_average_between _ _ E) as [E1 E2].
  apply tr;simple refine (existT _ (mkQpos ((abs (q - r) + ' e) / 2) _) _).
  { apply pos_mult_compat;[|solve_propholds].
    red. apply pos_plus_le_lt_compat_r;[solve_propholds|apply Qabs_nonneg].
  }
  simpl. exists (Qpos_diff _ _ E2).
  split.
  + apply pos_eq. exact (Qpos_diff_pr _ _ E2).
  + apply Qclose_alt. exact E1.
- apply (Trunc_ind _). intros [d [d' [He xi]]].
  apply Qclose_alt;rewrite He.
  apply Qclose_alt in xi.
  apply lt_le_trans with (' d);trivial.
  apply nonneg_plus_le_compat_r. solve_propholds.
Qed.

Global Instance Q_premetric@{} : PreMetric Q.
Proof.
split;try apply _.
intros e u;apply Qclose_alt. rewrite plus_negate_r.
unfold abs. rewrite (fst (abs_sig 0).2).
- solve_propholds.
- reflexivity.
Qed.

Global Instance Qneg_nonexpanding@{} : NonExpanding ((-) : Negate Q).
Proof.
intros e x y.
apply Qclose_neg.
Defined.


Global Instance Qplus_nonexpanding_l@{} : forall s : Q, NonExpanding (+ s).
Proof.
red. unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : q + s - (r + s) = q - r)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;trivial.
Qed.

Global Instance Qplus_nonexpanding_r@{} : forall s : Q, NonExpanding (s +).
Proof.
red;unfold close,Q_close;simpl. intros s e q r E.
assert (Hrw : s + q - (s + r) = q - r)
  by abstract ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;trivial.
Qed.

Global Instance Qabs_nonexpanding : NonExpanding (abs (A:=Q)).
Proof.
intros e q r xi.
apply Qclose_alt in xi;apply Qclose_alt.
apply le_lt_trans with (abs (q - r));trivial.
apply Qabs_triangle_alt.
Qed.

Global Instance Qmeet_nonexpanding_l : forall s : Q, NonExpanding (⊓ s).
Proof.
intros s e q r xi.
apply Qclose_alt;apply Qclose_alt in xi.
apply le_lt_trans with (abs (q - r));trivial. clear xi.
destruct (total le q s) as [E1|E1], (total le r s) as [E2|E2];
rewrite ?(meet_l _ _ E1), ?(meet_r _ _ E1), ?(meet_l _ _ E2), ?(meet_r _ _ E2).
- reflexivity.
- rewrite (Qabs_of_nonpos (q - r))
  by (apply (snd (flip_nonpos_minus _ _)); transitivity s;trivial).
  rewrite <-negate_swap_r.
  rewrite (Qabs_of_nonpos _ (snd (flip_nonpos_minus _ _) E1)).
  rewrite <-negate_swap_r.
  apply (order_preserving (+ (- q))).
  trivial.
- rewrite (Qabs_of_nonneg (q - r))
  by (apply (snd (flip_nonneg_minus _ _)); transitivity s;trivial).
  rewrite (Qabs_of_nonneg _ (snd (flip_nonneg_minus _ _) E2)).
  apply (order_preserving (+ (- r))). trivial.
- rewrite plus_negate_r,Qabs_of_nonneg by reflexivity.
  apply Qabs_nonneg.
Qed.

Global Instance Qmeet_nonexpanding_r : forall s : Q, NonExpanding (s ⊓).
Proof.
intros s e q r xi.
pose proof meet_sl_order_meet_sl.
rewrite !(commutativity s).
apply (non_expanding (fun x => meet x s)). trivial.
Qed.

Global Instance Qjoin_nonexpanding_l : forall s : Q, NonExpanding (⊔ s).
Proof.
intros s e q r xi.
apply Qclose_alt;apply Qclose_alt in xi.
apply le_lt_trans with (abs (q - r));trivial. clear xi.
destruct (total le q s) as [E1|E1], (total le r s) as [E2|E2];
rewrite ?(join_l _ _ E1), ?(join_r _ _ E1), ?(join_l _ _ E2), ?(join_r _ _ E2).
- rewrite plus_negate_r,Qabs_of_nonneg by reflexivity.
  apply Qabs_nonneg.
- rewrite (Qabs_of_nonpos (q - r))
  by (apply (snd (flip_nonpos_minus _ _)); transitivity s;trivial).
  rewrite <-negate_swap_r.
  rewrite (Qabs_of_nonpos _ (snd (flip_nonpos_minus _ _) E2)).
  rewrite <-negate_swap_r.
  apply (order_preserving (r +)).
  apply (snd (flip_le_negate _ _)). trivial.
- rewrite (Qabs_of_nonneg (q - r))
  by (apply (snd (flip_nonneg_minus _ _)); transitivity s;trivial).
  rewrite (Qabs_of_nonneg _ (snd (flip_nonneg_minus _ _) E1)).
  apply (order_preserving (q +)).
  apply (snd (flip_le_negate _ _)). trivial.
- reflexivity.
Qed.

Global Instance Qjoin_nonexpanding_r : forall s : Q, NonExpanding (s ⊔).
Proof.
intros s e q r xi.
pose proof join_sl_order_join_sl.
rewrite !(commutativity s).
apply (non_expanding (fun x => join x s)). trivial.
Qed.

Global Instance Qmult_lipschitz@{} : forall q : Q, Lipschitz (q *.) (pos_of_Q q).
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

Global Instance Qpos_upper_close e : Closeness (Qpos_upper e)
  := fun n x y => close n x.1 y.1.
Arguments Qpos_upper_close _ _ _ _ /.

Global Instance Q_recip_lipschitz (e : Q+)
  : Lipschitz ((/) ∘ pr1 ∘ (Qpos_upper_inject e)) (/ (e * e)).
Proof.
intros n q r xi.
unfold compose;simpl. apply Qclose_alt.
assert (PropHolds (0 < join q (' e))) as E
  by (apply lt_le_trans with (' e);[solve_propholds|apply join_ub_r]).
apply (strictly_order_reflecting ((join q (' e)) *.)).
assert (PropHolds (0 < join r (' e))) as E'
  by (apply lt_le_trans with (' e);[solve_propholds|apply join_ub_r]).
apply (strictly_order_reflecting ((join r (' e)) *.)).
set (X := join r (' e)) at 2 3.
rewrite <-(Qabs_of_nonneg (join r _)) by solve_propholds.
set (Y := join q (' e)) at 2 3.
rewrite <-(Qabs_of_nonneg (join q _)) by solve_propholds.
rewrite <-!Qabs_mult.
rewrite !(plus_mult_distr_l (Aplus:=Qplus)).
rewrite dec_recip_inverse by (apply irrefl_neq,symmetric_neq in E;trivial).
rewrite mult_1_r.
assert (Hrw :  (r ⊔ ' e) * ((q ⊔ ' e) * - / (r ⊔ ' e)) = - Y * (X / X))
  by ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;clear Hrw.
rewrite dec_recip_inverse by (apply irrefl_neq,symmetric_neq in E';trivial).
rewrite mult_1_r. unfold X, Y.
eapply lt_le_trans.
- apply Qclose_alt. eapply (non_expanding (⊔ ' e)). Symmetry. apply xi.
- transitivity (' (((e * e) / (e * e)) * n)).
  + rewrite pos_recip_r,Qpos_mult_1_l;reflexivity.
  + rewrite <-!Qpos_mult_assoc.
    change (' (e * (e * (/ (e * e) * n)))) with (' e * (' e * ' (/ (e * e) * n))).
    apply mult_le_compat;try solve_propholds;[apply join_ub_r|].
    apply mult_le_compat;try solve_propholds;[apply join_ub_r|].
    reflexivity.
Qed.

End rationals.

Section cauchy.
Universe UA.
Context {A : Type@{UA} } `{Closeness A}.

Record Approximation@{} :=
  { approximate :> Q+ -> A
  ; approx_equiv : forall d e, close (d+e) (approximate d) (approximate e) }.

Definition IsLimit@{} (x : Approximation) (l : A) :=
  forall e d : Q+, close (e+d) (x d) l.

Context `{!PreMetric A}.

Lemma limit_unique : forall x l1 l2, IsLimit x l1 -> IsLimit x l2 -> l1 = l2.
Proof.
intros x l1 l2 E1 E2.
apply separated.
intros e. rewrite (pos_split2 e),(pos_split2 (e/2)).
apply triangular with (x (e / 2 / 2));[Symmetry;apply E1|apply E2].
Qed.

Class Lim := lim : Approximation -> A.

Class CauchyComplete {Alim : Lim}
  := cauchy_complete : forall x, IsLimit x (lim x).

Context {Alim : Lim} `{!CauchyComplete}.

Lemma equiv_through_approx : forall u (y : Approximation) e d,
  close e u (y d) -> close (e+d) u (lim y).
Proof.
intros u y e d xi.
pose proof (cauchy_complete y) as E1;red in E1.
apply (merely_destruct ((fst (rounded _ _ _) xi))).
intros [d0 [d' [He E2]]].
pose proof (triangular _ _ _ _ _ E2 (E1 (d' / 2) _)) as E3.
eapply rounded_le;[exact E3|].
rewrite He.
clear u y e xi E1 He E2 E3.
set (D2' := d' / 2);rewrite (pos_split2 d');unfold D2';clear D2'.
apply flip_nonneg_minus.
assert (Hrw : ' (d0 + (d' / 2 + d' / 2) + d) - ' (d0 + (d' / 2 + d))
  = ' (d' / 2)) by ring_tac.ring_with_integers (NatPair.Z nat).
rewrite Hrw;solve_propholds.
Qed.

End cauchy.

End contents.

Arguments rounded_le {_ _ A _ _} e u v _ d _.
Arguments non_expanding {A _ B _} f {_ e x y} _.
Arguments lipschitz {A _ B _} f L {_ e x y} _.
Arguments uniform {A _ B _} f mu {_} _ _ _ _.
Arguments continuous {A _ B _} f {_} _ _.

Arguments map2_nonexpanding {A _ B _ C _ D _} f g {_ _} e x y xi.
Arguments map2_lipschitz {_ _ A _ B _ C _ D _} f g {_ _} Lf Lg {_ _} e x y xi.
Arguments map2_continuous {_ _ A _ B _ C _ D _} f g {_ _ _ _} u e.

Arguments Interval_close {_ _ _} _ _ _ _ _ /.

Arguments Lim A {_}.
Arguments lim {A _ _} _.

Arguments Approximation A {_}.
Arguments CauchyComplete A {_ _}.
